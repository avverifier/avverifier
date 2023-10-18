from mythril.ethereum import util
from mythril.disassembler import asm
from collections import defaultdict
from typing import ByteString, Dict, List, Tuple
import re
from stack import EVMStack, EVMMemory, SYMBOLIC_default, EVMStorage, SymbolicValue
from copy import deepcopy
from tqdm import tqdm
import signal
import time

def is_function_end(instruction: dict, instruction_list: list) -> bool:
    index = instruction_list.index(instruction)
    if index == len(instruction_list) - 1:
        return True

class Disassembly(object):
    def __init__(self, code: str):
        self.bytecode = code
        self.bytecode_nocon = self.remove_constructor(self.bytecode)
        if type(code) == str:
            self.instruction_list = asm.disassemble(util.safe_decode(code))
        else:
            self.instruction_list = asm.disassemble(code)
        self.func_hashes = []  # type: List[str]
        self.function_name_to_address = {}  # type: Dict[str, int]
        self.address_to_function_name = {}  # type: Dict[int, str]
        self.past2next = dict()
        self.next2past = dict()
        self.assign_bytecode(bytecode=self.bytecode_nocon)
        self.block_list = list()
        self.start_addr2id = dict()
        self.block_id = -1
        self.end_addr = self.instruction_list[-1]['address']
        self.issue_list = list()
        self.issue_list_caller = list()
        self.execution_time = 10

    def is_function_end(self, address):
        if address == self.end_addr:
            return True
        else:
            return False    

    def next_block_id(self):
        self.block_id += 1
        return self.block_id

    def remove_constructor(self, bytecode: str) -> str:
        constructor_pattern = re.compile(r"39(.*?)f3(.*?)60806040", re.DOTALL)
        match = constructor_pattern.search(bytecode)
        if match:
            cleaned_bytecode = bytecode[match.end() - len("60806040"):]
        else:
            cleaned_bytecode = bytecode
        return cleaned_bytecode

    def divide_into_basic_blocks(self, instruction_list):
        basic_blocks = []
        block_start = 0

        for i, instruction in enumerate(instruction_list):
            is_block_start = False

            # Case 1: First instruction in the list
            if i == 0:
                is_block_start = True
            # Case 2: JUMPDEST instruction
            elif instruction["opcode"] == "JUMPDEST":
                is_block_start = True
            # Case 3: Instruction after JUMPI
            elif instruction_list[i - 1]["opcode"] in ("JUMPI", "JUMP", "STOP", "RETURN"):
                is_block_start = True

            if is_block_start:
                if i > block_start:
                    basic_blocks.append(instruction_list[block_start:i])
                    block_start = i

        # Add the last block
        if block_start < len(instruction_list):
            basic_blocks.append(instruction_list[block_start:])

        return basic_blocks

    def assign_bytecode(self, bytecode):
        self.bytecode = bytecode
        self.instruction_list = asm.disassemble(bytecode)
        jump_table_indices = asm.find_op_code_sequence(
            [("PUSH1", "PUSH2", "PUSH3", "PUSH4"), ("EQ",)], self.instruction_list
        )

        for index in jump_table_indices:
            function_hash, jump_target, function_name = get_function_info(
                index, self.instruction_list
            )

            self.func_hashes.append(function_hash)


            if jump_target is not None and function_name is not None:
                self.function_name_to_address[function_name] = jump_target
                self.address_to_function_name[jump_target] = function_name


    def get_easm(self):
        return asm.instruction_list_to_easm(self.instruction_list)

    def run(self):
        basic_block = self.divide_into_basic_blocks(self.instruction_list)
        for item in basic_block:
            current_blockid = self.next_block_id()
            current_block = Block(current_blockid, item)
            self.block_list.append(current_block)
            self.start_addr2id[current_block.start_addr] = current_blockid
            if current_block.jump_target:
                self.past2next[current_block.start_addr] = current_block.jump_target
                self.next2past[current_block.jump_target] = current_block.start_addr

        for i, item in enumerate(self.block_list):
            start_addr = item.start_addr
            target_addr = item.jump_target
            if target_addr and target_addr in self.start_addr2id:
                target_id = self.start_addr2id[target_addr]
                item.get_nextid(target_id)
                self.block_list[target_id].get_pastid(i)

                if target_addr in self.address_to_function_name:
                    self.block_list[target_id].func_name = self.address_to_function_name[target_addr]
                if item.func_name != 'fallback':
                    self.block_list[target_id].func_name = item.func_name

    def check_msg_sender_equality(self, instruction_list: list) -> bool:
        is_msg_sender_loaded = False
        for instruction in instruction_list:
            if instruction["opcode"] == "CALLER":
                is_msg_sender_loaded = True
            if is_msg_sender_loaded and instruction["opcode"] == "EQ":
                return True
        return False

    def check_opcode(self, instruction_list, opcode):
        for item in instruction_list:
            if opcode == item["opcode"]:
                return True
        
        return False

    def get_issue(self, instruction, evmstack, stack_end_flag, memory):

        res = False 
        state_change = False 

        for id in evmstack.calldataload_list:
            if id not in evmstack.sha3_list and stack_end_flag and id not in evmstack.uncheck_list:
                evmstack.uncheck_list.append(id)
        if stack_end_flag and len(evmstack.uncheck_list) > 0 and not evmstack.check_caller:
            reserve_control_dict = dict()
            reserve_control_dict["SSTORE"], reserve_control_dict["CALL"]= -1, -1

            temp_control_dict = deepcopy(evmstack.control_dict)

            all_callid = list()
            for item in temp_control_dict:
                if temp_control_dict[item] == "CALL":
                    all_callid.append(evmstack.call_uidmap[item])

            for item in temp_control_dict:
                #只判断call
                #开始判断call，当前call的参数里一定要带有calldata，并且这个calldata必须是address
                if temp_control_dict[item] == "CALL":

                    try:
                        call_id = evmstack.call_uidmap[item]
                        call_para = evmstack.call_para[call_id]
                    except:
                        call_para = list()
                    real_call = True

                    for single_call in all_callid:
                        if single_call in call_para:
                            real_call = False

                    for single_para in call_para:
                        if single_para in evmstack.call_list and single_para in evmstack.address_id:
                            real_call = False
                            '''
                            if len(set(evmstack.call_order[:order] + call_para)) == len(evmstack.call_order[:order]) + len(call_para):
                                real_call = True
                            '''
                    if real_call == False:
                        evmstack.control_dict.pop(item)
                        continue


            for item in evmstack.control_dict:
                value = item
                key = evmstack.control_dict[item]
                reserve_control_dict[key] = value

            for unckecked_id in evmstack.uncheck_list:
                if reserve_control_dict[unckecked_id] < reserve_control_dict["SSTORE"] or reserve_control_dict[unckecked_id] < reserve_control_dict["CALL"]:
                    res = True
        return res

    def get_issue_list(self, instruction, stack, memory):
        res = False 
        if instruction["opcode"] in ("CALL", "STATICCALL", "DELEGATECALL"):
            addr = stack[-2]
            if isinstance(addr, SYMBOLIC_default) and addr.annotation == "CALLDATALOAD":
                current_uid = addr.uid
                if current_uid not in memory.sha3_list:
                    res = True
        return res

    def execute_block(self, block_id: int, initial_stack = None, evmmemory: EVMMemory = None, evmstorage = None):
        evmstack = EVMStack()
        if initial_stack != None:
            evmstack.stack = initial_stack

        if evmmemory is None :
            evmmemory = EVMMemory()
            evmmemory.mstore("0x40", "0x80")

        if evmstorage is None:
            evmstorage = EVMStorage()

        stack = [(block_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage))]
        stack_length = 1
        all_blockid = list()
        id2id = dict()
        is_end = False
        is_added = False
        calldataload_end, has_address_calldata = False, False
        current_issue = list()

        self.temp_state_change = {
            "CALLDATALOAD": list(),
            "CALL": False,
            "SSTORE": False,
            "CALLER_check": False,
            "SHA3": list(),
            "UNCHECKED": list(),
            "control_dict": dict(),
            "caller_index": None,
            "revert": False
        }
        loop_count = 0
        while stack and not is_end:
            loop_count += 1
            if loop_count > 2000:
                is_end = True
            block_id, evmstack, evmmemory, evmstorage = stack.pop()
            current_block = self.block_list[block_id]
            current_instruction = current_block.instruction_list
            all_blockid.append(block_id)

            if self.check_opcode(current_instruction, "REVERT") or self.check_opcode(current_instruction, "INVALID"):
                continue
            
            if evmstack.check_caller:
                break
            if evmstack.calldataload_end:
                calldataload_end = True
            if evmstack.has_address_calldata:
                has_address_calldata = True
            if calldataload_end and not has_address_calldata:
                pass
                #break
            check_msgsender = self.check_msg_sender_equality(current_instruction)
            for item in current_instruction:
                if item["opcode"] in ("STOP", "RETURN") and self.get_issue(item, evmstack, True, evmmemory):
                    is_end = True

                if item["address"] in self.address_to_function_name:
                    current_func = "_function_" + initial_stack[0]
                    if current_func != self.address_to_function_name[item["address"]]:
                        evmstack.close_dataload()
                self.get_issue(item, evmstack, False, evmmemory)
                if "argument" in item:
                    evmstack.execute(item["opcode"], value = item["argument"], memory = evmmemory, storage = evmstorage)
                else:
                    evmstack.execute(item["opcode"], memory = evmmemory, storage = evmstorage)

            if self.is_function_end(item['address']):
                break
            if evmstack.error_occurred:
                break
            evmstack_jumptarget = evmstack.jump_target if len(evmstack.jump_target) > 0 else None
            if item["opcode"] == "JUMP" and evmstack_jumptarget[0] != None:
                current_block.jump_target = int(evmstack_jumptarget[0], 16)
                if current_block.jump_target in self.start_addr2id:
                    next_id = self.start_addr2id[current_block.jump_target]
                    next_block = self.block_list[next_id]
                    next_instruction = next_block.instruction_list
                    if self.check_opcode(next_instruction, "REVERT") or self.check_opcode(next_instruction, "INVALID"):
                        assert 1
                        '''
                        if evmstack.load_caller:
                            break
                        '''
                        #self.temp_state_change["revert"] = True
                        continue
                    stack.append((next_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                    #print((block_id, next_id))
            elif item["opcode"] == "JUMPI":
                can_append_unsat = False
                can_append_next = False 

                if evmstack_jumptarget[0] == "next_id_unsatisfied":
                    # 添加条件不满足时的跳转地址
                    next_addr_unsatisfied = item["address"] + 1
                    next_id_unsatisfied = self.start_addr2id[next_addr_unsatisfied]
                    temp_id2id = (block_id, next_id_unsatisfied)

                    if temp_id2id not in id2id:
                        id2id[temp_id2id] = 1
                    else:
                        id2id[temp_id2id] += 1
                    if id2id[temp_id2id] <= 30:
                        can_append_unsat = True

                if evmstack_jumptarget[-1] != "next_id_unsatisfied":

                    current_block.jump_target = int(evmstack_jumptarget[-1], 16)
                    #if current_block.jump_target in self.start_addr2id and not check_msgsender:
                    if current_block.jump_target in self.start_addr2id:
                        next_id = self.start_addr2id[current_block.jump_target]
                        temp_id2id = (block_id, next_id)
                        if temp_id2id not in id2id:
                            id2id[temp_id2id] = 1
                        else:
                            id2id[temp_id2id] += 1
                        if id2id[temp_id2id] <= 30:
                            can_append_next = True

                if can_append_unsat and can_append_next:
                    
                    len_next = len(self.block_list[next_id].instruction_list)
                    len_unsat = len(self.block_list[next_id_unsatisfied].instruction_list)
                    if len_next > len_unsat:
                        #print(current_block.block_id, next_id_unsatisfied, next_id)
                        stack.append((next_id_unsatisfied, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                        stack.append((next_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                    else:
                        #print(current_block.block_id, next_id, next_id_unsatisfied)
                        stack.append((next_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                        stack.append((next_id_unsatisfied, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                elif can_append_next:
                    stack.append((next_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
                elif can_append_unsat:
                    stack.append((next_id_unsatisfied, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))

                    #print(temp_id2id)
            
            elif item["opcode"] not in ("JUMP", "JUMPI", "STOP", "RETURN"):
                next_addr = item["address"] + 1
                if item["opcode"].startswith("PUSH"):
                    next_addr += int(item["opcode"][4:])
                next_id = self.start_addr2id[next_addr]
                stack.append((next_id, deepcopy(evmstack), deepcopy(evmmemory), deepcopy(evmstorage)))
            item1 = [item[0] for item in stack]
            repeat = find_repeating_subsequence(item1)
            if repeat != None:
                stack = stack[:repeat[1] + repeat[2]]
                item1 = [item[0] for item in stack]
            stack_length = len(stack)
            #self.check_loop(stack)

        if self.get_issue(item, evmstack, True, evmmemory) and not evmstack.error_occurred:
            print("get issue:     ", initial_stack[0])
            self.issue_list.append(initial_stack[0])

    def process_bytecode(self, bytecode):
        self.run()

        for i, func in enumerate(self.function_name_to_address):
            try:
                addr = self.function_name_to_address[func]
                id = self.start_addr2id[addr]
                self.execute_block(id, [self.func_hashes[i]])
            except Exception as e:
                pass

    @classmethod
    def process_and_disassemble_bytecode(cls, bytecode):
        disassemble = cls(bytecode)
        disassemble.process_bytecode(bytecode)
        return disassemble

class Block(object):
    def __init__(self, block_id, instruction_list, func_name = 'fallback'):
        self.block_id = block_id
        self.start_addr = instruction_list[0]['address']
        self.end_addr = instruction_list[-1]['address']
        self.instruction_list = instruction_list
        self.func_name = func_name
        self.get_jump_target()
        self.nextid = None
        self.pastid = None
    
    def get_jump_target(self):
        if self.instruction_list[-1]['opcode'] in ('JUMP', 'JUMPI'):
            try:
                self.jump_target = int(self.instruction_list[-2]['argument'], 16)
            except:
                self.jump_target = None
        else:
            self.jump_target = None

    def get_pastid(self, past_id):
        self.pastid = past_id

    def get_nextid(self, next_id):
        self.nextid = next_id

def detect_loops_from_executed_blocks(block_ids: list):
    loop_blocks = []
    block_id_stack = []

    for block_id in block_ids:
        if block_id in block_id_stack:
            loop_start_index = block_id_stack.index(block_id)
            loop_block_ids = block_id_stack[loop_start_index:]
            loop_blocks.append(loop_block_ids)
            block_id_stack = block_id_stack[:loop_start_index + 1]
        else:
            block_id_stack.append(block_id)

    # 将循环的第一个基本块移除
    for loop_block in loop_blocks:
        loop_block.pop(0)

    return loop_blocks

def add_dict(mydict, value):
    dict_length = len(mydict)
    mydict[dict_length] = value

def find_repeating_subsequence(seq):
    n = len(seq)
    for window_size in range(2, n // 2 + 1):
        for i in range(n - 2 * window_size + 1):
            if seq[i:i+window_size] == seq[i+window_size:i+2*window_size]:
                return seq[i:i+window_size], i, window_size
    return None

def get_function_info(
    index: int, instruction_list: list
) -> Tuple[str, int, str]:

    if type(instruction_list[index]["argument"]) == tuple:
        try:
            function_hash = "0x" + bytes(
                instruction_list[index]["argument"]
            ).hex().rjust(8, "0")
        except AttributeError:
            raise ValueError(
                "Mythril currently does not support symbolic function signatures"
            )
    else:
        function_hash = "0x" + instruction_list[index]["argument"][2:].rjust(8, "0")


    function_name = "_function_" + function_hash

    try:
        offset = instruction_list[index + 2]["argument"]
        if type(offset) == tuple:
            offset = bytes(offset).hex()
        entry_point = int(offset, 16)
    except (KeyError, IndexError):
        return function_hash, None, None

    return function_hash, entry_point, function_name

if __name__ == '__main__':
    with open("./test_ca.txt", 'r') as f:
        bytecode = f.read()
    
    disassemble = Disassembly.process_and_disassemble_bytecode(bytecode)
    '''
    disassemble = Disassembly(bytecode)
    disassemble.run()
    disassemble.execute_block(93, ["0x490e6cbc"])
    '''
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    

    
    

    
    
    
    