"""
This module contains the detection code for potentially insecure low-level
calls that forward all gas to the callee without proper checks.
"""

import logging
from os import stat
from z3 import sat
from copy import copy
from mythril.analysis import solver
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.laser.ethereum.state.annotation import StateAnnotation as Annotation
from mythril.analysis.potential_issues import (
    PotentialIssue,
    get_potential_issues_annotation,
)
from mythril.analysis.swc_data import REENTRANCY
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.exceptions import UnsatError
from mythril.laser.smt import UGT, symbol_factory, Or, BitVec, Not
from mythril.laser.smt import symbol_factory, Solver
import itertools
from mythril.laser.ethereum.instructions import AddressAnnotation

log = logging.getLogger(__name__)

DESCRIPTION = """
Search for storage check with unrestricted gas to a user-specified address.
"""

class SHA3Annotation(Annotation):
    def __init__(self, address):
        self.uid = list(address.annotations)[0].uid


class StorageCheck(DetectionModule):
    """This module searches for low level calls (e.g. call.value()) that
    forward all gas to the callee."""

    name = "Storage Check to another contract"
    swc_id = REENTRANCY
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["SHA3", "CALL", "STATICCALL", "CALLDATALOAD"]
    #post_hooks = ["CALLDATALOAD"]

    def __init__(self):
        super().__init__()
        self.sha3list = []
        self.calldataloadlist = []
        self.ignore_fc = []

    def _execute(self, state: GlobalState) -> None:
        if state.environment.active_function_name == "_function_0x2fb316cc":
            a = 1
        if self._check_opcode(state, "SHA3"):
            address = state.mstate.memory.get_word_at(0)
            #annotation = AddressAnnotation(address, state.environment.active_function_name)
            #state.annotate(annotation)
            try:
                annotation = SHA3Annotation(address)
                state.annotate(annotation)
            except:
                pass
            self.sha3list.append(state)
            return

        if self._check_calldataload(state):
            address = state.mstate.stack[-1]
            #state.annotate(AddressAnnotation(address, state.environment.active_function_name))
            self.calldataloadlist.append(state)
            return            

        if not (self._check_opcode(state, "CALL") or self._check_opcode(state, "STATICCALL")):
            return
        potential_issues = self._analyze_state(state)
        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(potential_issues)

    def _check_opcode(self, state, opcode: str) -> bool:
        start_addr = state.node.start_addr
        end_addr = state.node.end_addr
        return any(_opcode['opcode'] == opcode for _opcode in state.environment.code.instruction_list[start_addr:end_addr+1])

    def _check_calldataload(self, state) -> bool:
        if not self._check_opcode(state, "CALLDATALOAD"):
            return False
        check_opcode = ["DUP2", "AND"]
        instruction_list = state.environment.code.instruction_list[state.node.start_addr:state.node.end_addr+1]
        for i, _opcode in enumerate(instruction_list):
            if _opcode['opcode'] == "DUP2":
                if all(instruction_list[i+j]['opcode'] == opcode for j, opcode in enumerate(check_opcode)):
                    return True
        return False

    def check_is_not_fixed(self, addr):
        #构建约束 addr1 == to, addr2 == to，如果上述条件满足，则求解下面的约束
        solver = Solver()
        addr1 = symbol_factory.BitVecSym("address1", 256)
        addr2 = symbol_factory.BitVecSym("address2", 256)
        solver.add(addr1 == addr)
        solver.add(addr2 == addr)
        result = solver.check()
        #addr1 != addr2        
        if result == sat:

            # 检查 addr1 != addr2 是否有解
            solver = Solver()
            solver.add(addr1 != addr2)

            result = solver.check()

            if result == sat:
                return True
            else:
                return False
        else:
            return False

    def _analyze_state(self, state: GlobalState) -> list:
        current_function_name = state.environment.active_function_name
        if current_function_name == "_function_0x2fb316cc":
            a = 1

        if current_function_name in {"constructor", "fallback"}:
            return []

        address = state.get_current_instruction()["address"]

        issue = PotentialIssue(
            contract=state.environment.active_account.contract_name,
            function_name=current_function_name,
            address=address,
            swc_id=REENTRANCY,
            title="Without Check before Call To User-Supplied Address",
            bytecode=state.environment.code.bytecode,
            severity="High",
            description_head="A call to a user-supplied address is executed.",
            description_tail="Without Check before Call",
            detector=self,
        )

        #sha3_same_function = any(state.environment.active_function_name == current_function_name for state in self.sha3list)
        calldataload_same_function = any(state.environment.active_function_name == current_function_name for state in self.calldataloadlist)
        #要排除call的地址不是一个固定的地址
        # 这里判断如果该函数没有address参数，就返回
        if not calldataload_same_function:
            return []
        to = state.mstate.stack[-2]
        is_fixed = self.check_is_not_fixed(to)
        #is fixed如果为真，说明to地址被固定，calldata无意义，容易判断为假阳
        if not is_fixed:
            #地址固定，不用判断
            return []
        no_sha3_flag = False
        try:
            current_addr_anno = list(to.annotations)[0]
            current_addr_uid = current_addr_anno.uid
            if len(self.sha3list) > 0:
                address_annotations = [
                    annotation
                    for annotation in self.sha3list[-1].annotations
                    if (
                        isinstance(annotation, SHA3Annotation)
                        and annotation.uid == current_addr_uid and annotation.function_name == current_function_name
                    )
                ]

                if len(address_annotations) == 0:
                    no_sha3_flag = True
            else:
                no_sha3_flag = True
        except:
            pass

        # 这里判断如果call之前没有sha3，说明没有检测，就可以输出issue
        if no_sha3_flag:
            log.debug(f"[ISSUE DETECTED] {issue.function_name}")
            return [issue]
        '''
        sha3_constraint = [state.mstate.memory.get_word_at(0) == ACTORS.attacker for state in self.sha3list if state.environment.active_function_name == current_function_name]
        constraints = Constraints([to == ACTORS.attacker] + sha3_constraint)
        try:
            solver.get_transaction_sequence(
                state, constraints + state.world_state.constraints
            )
            return []
        except UnsatError:
            log.debug("[EXTERNAL_CALLS] No model found.")
        '''
        return []

detector = StorageCheck()

