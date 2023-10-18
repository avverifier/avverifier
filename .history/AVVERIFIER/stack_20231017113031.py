from copy import deepcopy
import itertools
from z3 import BitVec, Bool, Array, BitVecSort, BitVecVal, Store
from z3.z3 import Solver

class SYMBOLIC_default:
    def __init__(self, annotation=""):
        self.annotation = annotation
        self.uid = next(SYMBOLIC_default.uid_generator)

    def __repr__(self):
        return "({})".format(self.annotation)

    uid_generator = itertools.count()

class SymbolicValue(SYMBOLIC_default):
    def __init__(self, type, size=None, annotation="", taint = None, sload_taint = list()):
        super().__init__(annotation)
        self.type = type
        self.size = size
        self.value = self._create_value()
        self.taint = taint
        self.sload_taint = sload_taint

    def _create_value(self):
        if self.type == 'bitvec':
            if self.size is None:
                #raise ValueError("Size must be specified for bitvec type")
                pass
            return BitVec(self.annotation, self.size)
        elif self.type == 'memory':
            return Array(self.annotation, BitVecSort(256), BitVecSort(8))
        elif self.type == 'bool':
            return Bool(self.annotation)
        else:
            #raise ValueError("Invalid type: " + self.type)
            pass

    def __repr__(self):
        return "<SymbolicValue: type={}, size={}, value={}, annotation={}>".format(
            self.type, self.size, self.value, self.annotation)

    def get_taint(self, taint):
        self.taint = taint



class EVMStack:
    def __init__(self, stack=[]):
        self.stack = stack
        self.sload_list = list()
        self.store_list = list()
        self.call_list = list()
        self.sha3_list = list()
        self.uncheck_list = list()
        self.calldataload_list = list()
        self.calldata_list = list()
        self.check_caller = False
        self.load_caller = False
        self.error_occurred = False
        self.calldataload_end = False
        self.constraint = Solver()
        self.has_address_calldata = False
        self.address_id = list()
        self.contract_map = dict()
        self.control_dict = dict()
        self.RETURNDATASIZE = None
        self.check_initial = dict()
        self.check_initial_list = dict()
        self.call_para = dict()
        self.call_order = list()
        self.call_uidmap = dict()
    def close_dataload(self):
        self.calldataload_end = True

    def get_hash(self):
        str_list = []
        for item in self.stack:
            if isinstance(item, SymbolicValue):
                str_list.append(str(item.uid))
            else:
                str_list.append(item)       

        return hash("".join(str_list))     

    def execute(self, opcode, value=None, memory=None, storage=None):
        try:
            if opcode == "JUMPDEST":
                pass
            elif opcode.startswith('PUSH'):
                # 获取要推送的值
                push_value = self._get_push_value(value)
                # 将值压入栈中
                self.stack.append(push_value)
            elif opcode.startswith('SWAP'):
                n = int(opcode[4:])
                self._swap(n)
            elif opcode == 'POP':
                self._pop()
            elif opcode.startswith('LOG'):
                n = int(opcode[3:])
                self._log(n)
            elif opcode.startswith('DUP'):
                n = int(opcode[3:])
                self._dup(n)
            elif opcode == 'MLOAD':
                offset = self._pop()
                try:
                    self._push(memory.mload(offset))
                except:
                    self._push(SymbolicValue('bitvec', 8, '0'))

            elif opcode.startswith('LOG'):
                n = int(opcode[3:])
                self._log(n)
                self.close_dataload()
            elif opcode == "JUMP":
                dest = self._pop()
                if isinstance(dest, SymbolicValue):
                    self.jump_target = [None]
                else:
                    self.jump_target = [dest]
            elif opcode == "CALLDATASIZE":
                calldatasize = SymbolicValue('bitvec', 256, 'CALLDATASIZE')
                self._push(calldatasize)

            elif opcode == 'SUB':
                # 从堆栈中弹出两个值
                a = self._pop()
                b = self._pop()
                
                # 检查弹出的值类型
                if isinstance(b, SYMBOLIC_default) or isinstance(a, SYMBOLIC_default):
                    # 如果有任一值是符号变量，创建一个新的符号变量表示减法结果
                    result = SymbolicValue('bool', annotation='sub_result')
                else:
                    # 如果两个值都是具体的数值，执行减法操作
                    result = int2hex((hex2int(a) - hex2int(b)) % (2 ** 256))
                    result = cut_0x(result)
                copy_taint(a,b, self.address_id, result)

                # 将减法结果压入堆栈
                self._push(result)
            elif opcode == "ISZERO":
                a = self._pop()
                if isinstance(a, SymbolicValue):
                    result = SymbolicValue('bool', annotation='iszero_result')
                else:
                    if hex2int(a) == 0:
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                #copy_taint(a, a, self.address_id, result)
                self._push(result)

            elif opcode == "SLT":
                a = self._pop()
                b = self._pop()
                if isinstance(a, SymbolicValue) and isinstance(b, SymbolicValue):
                    result = SymbolicValue('bool', annotation='SLT')
                    # 对具体数值进行普通比较
                elif isinstance(a, SymbolicValue) and isinstance(b, str):
                    if hex2int(b) == 0:
                        result = int2hex(0)
                    else:
                        result = SymbolicValue('bool', annotation='SLT')

                elif isinstance(b, SymbolicValue) and isinstance(a, str):
                    result = SymbolicValue('bool', annotation='SLT')                    
                elif isinstance(a, str) and isinstance(b, str):
                    if hex2int(a) < hex2int(b):
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                else:
                    result = SymbolicValue('bool', annotation='SLT')

                # 将比较结果推送回栈顶
                if not isinstance(result, str):
                    copy_taint(a,b, self.address_id, result)
                self._push(result)

            elif opcode == "SGT":
                a = self._pop()
                b = self._pop()
                if isinstance(a, SymbolicValue) and isinstance(b, SymbolicValue):
                    result = SymbolicValue('bool', annotation='SGT')
                elif isinstance(a, SymbolicValue) and isinstance(b, str):
                    result = SymbolicValue('bool', annotation='SGT')

                elif isinstance(b, SymbolicValue) and isinstance(a, str):
                    if hex2int(a) == 0:
                        result = int2hex(0)
                    else:
                        result = SymbolicValue('bool', annotation='SGT')  
                elif isinstance(a, str) and isinstance(b, str):
                    if hex2int(a) > hex2int(b):
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                    # 对具体数值进行普通比较
                else:
                    result = SymbolicValue('bool', annotation='SGT')  


                # 将比较结果推送回栈顶
                if not isinstance(result, str):
                    copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "OR":
                a = self._pop()
                b = self._pop()
                try:
                    result = int2hex(hex2int(a) | hex2int(b))
                    result = cut_0x(result)
                except:
                    if (isinstance(a, str) and hex2int(a) == 1) or (isinstance(b, str) and hex2int(b) == 1):
                        result = int2hex(1)
                    else:
                        result = SymbolicValue('bool', annotation='or_result')
                        copy_taint(a,b, self.address_id, result)
                self._push(result)

            elif opcode == "XOR":
                a = self._pop()
                b = self._pop()
                try:
                    result = int2hex(hex2int(a) ^ hex2int(b))
                except:
                    result = SymbolicValue('bool', annotation='xor_result')
                copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "GT":
                a = self._pop()
                b = self._pop()
                if isinstance(a, SymbolicValue) and isinstance(b, SymbolicValue):
                    result = SymbolicValue('bool', annotation='GT')
                elif isinstance(a, SymbolicValue) and isinstance(b, str):
                    result = SymbolicValue('bool', annotation='GT')

                elif isinstance(b, SymbolicValue) and isinstance(a, str):
                    if hex2int(a) == 0:
                        result = int2hex(0)
                    else:
                        result = SymbolicValue('bool', annotation='GT')  
                elif isinstance(a, str) and isinstance(b, str):
                    if hex2int(a) > hex2int(b):
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                    # 对具体数值进行普通比较
                else:
                    result = SymbolicValue('bool', annotation='GT')  


                # 将比较结果推送回栈顶
                if not isinstance(result, str):
                    copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "LT":
                a = self._pop()
                b = self._pop()
                if isinstance(a, SymbolicValue) and isinstance(b, SymbolicValue):
                    result = SymbolicValue('bool', annotation='LT')
                    # 对具体数值进行普通比较
                elif isinstance(a, SymbolicValue) and isinstance(b, str):
                    if hex2int(b) == 0:
                        result = int2hex(0)
                    else:
                        result = SymbolicValue('bool', annotation='LT')

                elif isinstance(b, SymbolicValue) and isinstance(a, str):
                    result = SymbolicValue('bool', annotation='LT')                    
                elif isinstance(a, str) and isinstance(b, str):
                    if hex2int(a) < hex2int(b):
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                else:
                    result = SymbolicValue('bool', annotation='LT')

                # 将比较结果推送回栈顶
                if not isinstance(result, str):
                    copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "DIV":
                a = self._pop()
                b = self._pop()
                if isinstance(b, str) and hex2int(b) == 1:
                    result = a
                elif isinstance(a, SymbolicValue) or isinstance(b, SymbolicValue):
                    result = SymbolicValue('bitvec', 256, 'DIV')
                    copy_taint(a,b, self.address_id, result)
                    # 对具体数值进行普通比较
                else:
                    try:
                        result = int2hex(hex2int(a) // hex2int(b))
                        result = cut_0x(result)
                    except:
                        result = int2hex(0)

                self._push(result)

            elif opcode == "SDIV":
                a = self._pop()
                b = self._pop()
                try:
                    result = int2hex(signed_div(hex2int(a), hex2int(b)))
                    result = cut_0x(result)
                    
                except:
                    result = SymbolicValue('bitvec', 256, 'SDIV')
                copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "MUL":
                a = self._pop()
                b = self._pop()
                if isinstance(a, SymbolicValue) or isinstance(b, SymbolicValue):
                    result = SymbolicValue('bitvec', 256, 'MUL')
                    # 对具体数值进行普通比较
                else:
                    result = int2hex((hex2int(a) * hex2int(b)) % 2 ** 256)
                    result = cut_0x(result)
                copy_taint(a,b, self.address_id, result)
                self._push(result)
                    
            elif opcode == "CALLDATALOAD":

                offset = self._pop()
                result = SymbolicValue('bitvec', 256, 'CALLDATALOAD')
                self.calldata_list.append(result.uid)
                self._push(result)
                
            elif opcode == "JUMPI":
                dest = self._pop()
                condition = self._pop()
                if isinstance(condition, SymbolicValue):
                    if condition.taint != None:
                        if condition.taint.annotation in ("CALLER", "CALLDATALOAD"):
                            self.jump_target = ["next_id_unsatisfied", dest]
                        else:
                            if isinstance(dest, SymbolicValue):
                                self.jump_target = ["next_id_unsatisfied"]
                            else:
                                self.jump_target = ["next_id_unsatisfied", dest]
                    else:
                        self.jump_target = ["next_id_unsatisfied", dest]

                    temp_uid = -1
                    if condition.annotation == "SLOAD":
                        temp_uid = condition.uid
                    elif condition.taint != None and condition.taint.annotation == "SLOAD":
                        temp_uid = condition.taint.uid

                    try:
                        self.check_initial[self.check_initial_list[temp_uid]] = True
                    except:
                        pass

                else:
                    if condition != int2hex(0) and not isinstance(dest, SymbolicValue):
                        self.jump_target = [dest]
                    elif condition == int2hex(0):
                        self.jump_target = ["next_id_unsatisfied"]
                    else:
                        self.jump_target = ["next_id_unsatisfied", dest]                    

            elif opcode == "SHL":
                shift_amount = self._pop()
                value = self._pop()

                if isinstance(shift_amount, SYMBOLIC_default) or isinstance(value, SYMBOLIC_default):
                    # 处理符号值的情况
                    result = SymbolicValue('bitvec', 256, 'SHL')
                else:
                    shift_amount = int(shift_amount.value) if isinstance(shift_amount, SymbolicValue) else int(shift_amount, 16)
                    value = int(value.value) if isinstance(value, SymbolicValue) else int(value, 16)
                    
                    if shift_amount < 0 or shift_amount >= 256:
                        result = int2hex(0)
                    else:
                        result = int2hex((value << shift_amount) & (2**256 - 1))
                        result = cut_0x(result)

                self._push(result)
            elif opcode == "SHR":
                shift_amount = self._pop()
                value = self._pop()

                if isinstance(shift_amount, SYMBOLIC_default) or isinstance(value, SYMBOLIC_default):
                    # 处理符号值的情况
                    result = SymbolicValue('bitvec', 256, 'SHR')
                else:
                    shift_amount = int(shift_amount.value) if isinstance(shift_amount, SymbolicValue) else int(shift_amount, 16)
                    value = int(value.value) if isinstance(value, SymbolicValue) else int(value, 16)
                    
                    if shift_amount < 0 or shift_amount >= 256:
                        result = int2hex(0)
                    else:
                        result = int2hex(value >> shift_amount)
                        result = cut_0x(result)

                self._push(result)

            elif opcode == "AND":
                a = self._pop()
                b = self._pop()
                pre_a = deepcopy(a)
                pre_b = deepcopy(b)
                mask = "ff"
                if isinstance(a, str) and mask in a and len(set(a[2:])) == 1:
                    self._push(pre_b)
                elif isinstance(b, str) and mask in b and len(set(b[2:])) == 1:
                    self._push(pre_a)
                else:
                    if not isinstance(a, SymbolicValue) and not isinstance(b, SymbolicValue):
                        # Perform bitwise AND operation on non-symbolic values
                        result = int2hex(int(a, 16) & int(b, 16))
                        result = cut_0x(result)
                        self._push(result)
                    else:
                        # Handle symbolic values or unsupported scenarios
                        self._push(SymbolicValue('bool', annotation='and_result'))

                if isinstance(a, SymbolicValue) and b == "0xffffffffffffffffffffffffffffffffffffffff":
                    self.has_address_calldata = True
                    if a.uid not in self.address_id:
                        self.address_id.append(a.uid)
                        self.contract_map[a.uid] = False
                elif isinstance(b, SymbolicValue) and a == "0xffffffffffffffffffffffffffffffffffffffff":
                    self.has_address_calldata = True
                    if b.uid not in self.address_id:
                        self.address_id.append(b.uid)
                        self.contract_map[b.uid] = False

            elif opcode == "EQ":
                a = self._pop()
                b = self._pop()
                pre_a = deepcopy(a)
                pre_b = deepcopy(b)
                if isinstance(a, SymbolicValue) and isinstance(b, SymbolicValue):
                    
                    if a.annotation == b.annotation and a.uid == b.uid:
                        result = int2hex(1)
                    elif (a.annotation == "CALLER" and b.annotation == "CALL_RETURN") or (b.annotation == "CALLER" and a.annotation == "CALL_RETURN"):
                        result = int2hex(1)
                    else:
                        #result = SymbolicValue('bool', annotation='eq_result')
                        result = SymbolicValue('bool', annotation='eq_result')
                        copy_taint(a,b, self.address_id, result)
                    if a.annotation == "CALLER" or b.annotation == "CALLER":
                        if (a.annotation == "CALLER" and b.annotation in ("CALLDATALOAD", "CALLRETURN")) or (b.annotation == "CALLER" and a.annotation in ("CALLDATALOAD", "CALLRETURN")):
                            pass
                        elif a.annotation == "CALLER" and b.taint != None and b.taint.annotation == "CALLDATALOAD":
                            pass
                        elif b.annotation == "CALLER" and a.taint != None and a.taint.annotation == "CALLDATALOAD":
                            pass
                        else:
                            self.check_caller = True
 
                    elif a.annotation == "CALLDATALOAD" or b.annotation == "CALLDATALOAD":
                        if a.annotation == "CALLDATALOAD" and b.annotation in ("SLOAD"):
                            #self.check_caller = True
                            self.sha3_list.append(a.uid)
                            pass
                        elif b.annotation == "CALLDATALOAD" and a.annotation in ("SLOAD"):
                            #self.check_caller = True
                            self.sha3_list.append(b.uid)
                            pass                            
                        elif a.annotation == "CALLDATALOAD" and b.taint != None and b.taint.annotation == "SLOAD":
                            #self.check_caller = True
                            self.sha3_list.append(a.uid)
                            pass   
                        elif b.annotation == "CALLDATALOAD" and a.taint != None and a.taint.annotation == "SLOAD":
                            #self.check_caller = True
                            self.sha3_list.append(b.uid)
                            pass   
                        else:
                            pass  
                    
                elif isinstance(a, SymbolicValue) and not isinstance(b, SymbolicValue):
                    if a.annotation in ("CALLDATALOAD", "CALLER"):
                        result = int2hex(0)
                    elif a.annotation == "SLOAD" and a.taint != None and a.taint.annotation in ("CALLDATALOAD", "CALLER"):
                        result = int2hex(0)
                    elif a.annotation == "CALL_RETURN" and a.taint != None and a.taint.annotation in ("CALLDATALOAD"):
                        result = int2hex(1)
                    else:
                        result = SymbolicValue('bool', annotation='eq_result')
                        copy_taint(a,a, self.address_id, result)
                elif isinstance(b, SymbolicValue) and not isinstance(a, SymbolicValue):
                    if b.annotation in ("CALLDATALOAD", "CALLER"):
                        result = int2hex(0)
                    elif b.annotation == "SLOAD" and b.taint != None and b.taint.annotation in ("CALLDATALOAD", "CALLER"):
                        result = int2hex(0)
                    elif b.annotation == "CALL_RETURN" and b.taint != None and b.taint.annotation in ("CALLDATALOAD"):
                        result = int2hex(1)
                    else:
                        result = SymbolicValue('bool', annotation='eq_result')
                        copy_taint(b,b, self.address_id, result)
                else:
                    if a == b:
                        result = int2hex(1)
                    else:
                        result = int2hex(0)
                self._push(result)
            elif opcode == "MULMOD":
                a = self._pop()
                b = self._pop()
                c = self._pop()
                try:
                    self._push(int2hex((hex2int(a) * hex2int(b)) % hex2int(c)))
                except:
                    self._push(SymbolicValue('bitvec', 256, 'MULMOD'))
                
            elif opcode == "MSTORE":
                offset = self._pop()
                value = self._pop()
                memory.mstore(offset, value)

            elif opcode == "MSTORE8":
                offset = self._pop()
                value = self._pop()
                try:
                    value = int2hex(hex2int(value) & 0XFF)
                except:
                    pass
                memory.mstore(offset, value)
 
            elif opcode == "SSTORE":
                offset = self._pop()
                value = self._pop()
                storage.sstore(offset, value)
                if isinstance(offset, SymbolicValue):

                    if offset.taint != None and offset.taint.annotation == "CALLER":
                        if offset.taint.uid not in self.store_list:
                            self.store_list.append(offset.taint.uid)
 
                    elif offset.taint != None and offset.taint.annotation == "CALLDATALOAD":
                        if offset.taint.uid not in self.sha3_list:
                            self.sha3_list.append(offset.taint.uid)

                if isinstance(value, SymbolicValue):
                    if value.taint != None and value.taint.annotation == "CALLER":
                        if value.taint.uid not in self.store_list:
                            self.store_list.append(value.taint.uid)
                    '''
                    elif value.taint != None and value.taint.annotation == "CALLDATALOAD":
                        if value.taint.uid not in self.sha3_list:
                            self.sha3_list.append(value.taint.uid)
                    '''
                self.close_dataload()

                if isinstance(offset, SymbolicValue) and offset.taint != None and offset.taint.annotation == "CALLER":
                    add_dict(self.control_dict, "SSTORE")
                elif isinstance(value, SymbolicValue) and value.taint != None and value.taint.annotation == "CALLER":
                    add_dict(self.control_dict, "SSTORE")
                try:
                    if self.check_initial[offset] == True and value == int2hex(1):
                        self.error_occurred = True
                except:
                    pass
            elif opcode == "SHA3":
                offset = self._pop()
                length = self._pop()
                cur_memory = memory.mload(offset)
                sload_list = list()
                if isinstance(length, str):
                    if int(hex2int(length) / 32) < 100:
                        for i in range(int(hex2int(length) / 32)):
                            load_offset = int2hex(hex2int(offset) + 32 * i)
                            temp_memory = memory.mload(load_offset)
                            if isinstance(temp_memory, SymbolicValue):
                                if temp_memory.annotation in ("CALLDATALOAD", "CALLER"):
                                    sload_list.append(temp_memory)
                                elif temp_memory.taint != None and temp_memory.taint.annotation in ("CALLDATALOAD", "CALLER"):
                                    sload_list.append(temp_memory.taint)
                if isinstance(cur_memory, SymbolicValue):
                    self._push(SymbolicValue('bitvec', 256, 'SHA3', cur_memory, sload_list))

                    
                else:
                    self._push(SymbolicValue('bitvec', 256, 'SHA3'))
                self.close_dataload()
            elif opcode == "SLOAD":
                key = self._pop()
                result = SymbolicValue('bitvec', 256, 'SLOAD')
                if isinstance(key, SymbolicValue):
                    
                    if key.sload_taint != []:
                        #self.constraint.add(key.taint.annotation != "CALLDATALOAD")
                        for item in key.sload_taint:
                            if item.annotation == "CALLDATALOAD":
                                if item.uid not in self.sload_list:
                                    self.sload_list.append(item.uid)
                                    self.sha3_list = list(set(self.sha3_list + self.sload_list))
                            
                            if item.annotation == "CALLER":
                                self.load_caller = True
                    if key.annotation in ("CALLDATALOAD", "CALLER"):
                        #result.get_taint(key)
                        result = int2hex(0)
                        #result = SymbolicValue('bitvec', 256, 'SLOAD', taint=key)
                    elif key.taint != None and key.taint.annotation in ("CALLDATALOAD", "CALLER"):
                        #result.get_taint(key.taint)
                        result = int2hex(0)
                        #result = SymbolicValue('bitvec', 256, 'SLOAD', taint=key.taint)
                self._push(result)
                self.close_dataload()

                if isinstance(key, str):
                    if key not in self.check_initial:
                        self.check_initial[key] = False
                    if result.uid not in self.check_initial_list:
                        self.check_initial_list[result.uid] = key
            elif opcode == "ADD":
                a = self._pop()
                b = self._pop()
                try:
                    result = int2hex(hex2int(a) + hex2int(b))
                    result = cut_0x(result)
                    
                except:
                    result = SymbolicValue('bitvec', 256, 'ADD')
                #if isinstance(a, SymbolicValue) and a.annotation == "CALLDATALOAD" or isinstance(b, SymbolicValue) and b.annotation == "CALLDATALOAD":

                #copy_taint(a,b, self.address_id, result, False)
                copy_taint(a,b, self.address_id, result)
                self._push(result)
            elif opcode == "EXTCODESIZE":
                self._pop()
                self._push(SymbolicValue('bitvec', 256, 'EXTCODESIZE'))
                self.close_dataload()
            elif opcode == "GAS":
                self._push(SymbolicValue('bitvec', 256, 'GAS'))
                self.close_dataload()
            elif opcode == "CALL":
                _, addr, _, argsoffset, length, offset, retlength = [self._pop() for _ in range(7)]
                if isinstance(retlength, str):
                    self.RETURNDATASIZE = int2hex(hex2int(retlength) + hex2int("0x20"))

                if isinstance(addr, SymbolicValue):
                    if addr.annotation == "CALLDATALOAD":
                        if addr.uid not in self.call_list and isinstance(length, str) and int(length, 16) != 0:
                            self.call_list.append(addr.uid)
                    if addr.taint == None:
                        taint = addr
                    else:
                        taint = addr.taint
                    memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN', taint)
                else:
                    if hex2int(addr) > 999999:
                        memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN')
                    else:
                        self.error_occurred = True

                self._push(int2hex(1))
                self.close_dataload()

                if isinstance(addr, SymbolicValue) and addr.annotation == "CALLDATALOAD":
                    current_uid = addr.uid
                    if current_uid not in self.calldataload_list and isinstance(length, str) and int(length, 16) != 0:
                        self.calldataload_list.append(current_uid)
                        add_dict(self.control_dict, current_uid)
                        add_dict(self.call_uidmap, current_uid)
                        self.call_order.append(current_uid)

                elif isinstance(addr, SymbolicValue) and addr.annotation == "CALLER":
                    current_uid = addr.uid
                    add_dict(self.control_dict, "CALLER")
                    add_dict(self.call_uidmap, current_uid)
                    self.call_order.append(current_uid)
                else:
                    if isinstance(length, str) and isinstance(addr, SymbolicValue):
                        if int(length, 16) != 0:
                            add_dict(self.control_dict, "CALL")
                            add_dict(self.call_uidmap, addr.uid)
                            self.call_order.append(addr.uid)
                            if isinstance(argsoffset, str):
                                if int(int(length, 16) / 32) < 100:
                                    for i in range(int(int(length, 16) / 32)):
                                        try:
                                            cur_offset = int2hex(hex2int(argsoffset) + i * 32 + 4)
                                            temp_para = memory.memory[cur_offset]
                                            if addr.uid not in self.call_para:
                                                self.call_para[addr.uid] = list()
                                            if temp_para.uid not in self.call_para:
                                                self.call_para[addr.uid].append(temp_para.uid)
                                            if isinstance(temp_para, SymbolicValue):
                                                if int(length, 16) <= 40:
                                                    if temp_para.annotation == "CALLER":
                                                        self.check_caller = True
                                                    elif temp_para.taint != None and temp_para.taint.annotation == "CALLER":
                                                        self.check_caller = True
                                        except:
                                            pass

                if isinstance(length, str):
                    if int(length, 16) != 0:
                        self.contract_map[addr.uid] = True


            elif opcode == "DELEGATECALL":
                _, addr, argsoffset, length, offset, retlength = [self._pop() for _ in range(6)]

                if isinstance(retlength, str):
                    self.RETURNDATASIZE = int2hex(hex2int(retlength) + hex2int("0x20"))
                if isinstance(addr, SymbolicValue):
                    if addr.annotation == "CALLDATALOAD":
                        if addr.uid not in self.call_list:
                            self.call_list.append(addr.uid)
                    if addr.taint == None:
                        taint = addr
                    else:
                        taint = addr.taint
                    memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN', taint)
                else:
                    if hex2int(addr) > 999999:
                        memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN')
                    else:
                        self.error_occurred = True

                self._push(int2hex(1))
                self.close_dataload()

                if isinstance(addr, SymbolicValue) and addr.annotation == "CALLDATALOAD":
                    current_uid = addr.uid
                    if current_uid not in self.calldataload_list:
                        self.calldataload_list.append(current_uid)
                        add_dict(self.control_dict, current_uid)
                        add_dict(self.call_uidmap, current_uid)
                        self.call_order.append(current_uid)

                else:
                    if isinstance(length, str) and isinstance(addr, SymbolicValue):
                        if int(length, 16) != 0:
                            add_dict(self.control_dict, "CALL")
                            add_dict(self.call_uidmap, addr.uid)
                            self.call_order.append(addr.uid)
                            if isinstance(argsoffset, str):
                                if int(int(length, 16) / 32) < 100:
                                    for i in range(int(int(length, 16) / 32)):
                                        try:
                                            cur_offset = int2hex(hex2int(argsoffset) + i * 32 + 4)
                                            temp_para = memory.memory[cur_offset]
                                            if addr.uid not in self.call_para:
                                                self.call_para[addr.uid] = list()
                                            if temp_para.uid not in self.call_para:
                                                self.call_para[addr.uid].append(temp_para.uid)
                                            if isinstance(temp_para, SymbolicValue):
                                                if int(length, 16) <= 40:
                                                    if temp_para.annotation == "CALLER":
                                                        self.check_caller = True
                                                    elif temp_para.taint != None and temp_para.taint.annotation == "CALLER":
                                                        self.check_caller = True
                                        except:
                                            pass


                if isinstance(length, str) and isinstance(addr, SymbolicValue):
                    if int(length, 16) != 0:
                        self.contract_map[addr.uid] = True

            elif opcode in ("CALLDATACOPY", "CODECOPY"):
                _, offset, length = [self._pop() for _ in range(3)]
              
                memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALLDATACOPY_RETURN')
                #self.close_dataload()

            elif opcode == "STATICCALL":
                _, addr, argsoffset, length, offset, retlength = [self._pop() for _ in range(6)]
                if isinstance(retlength, str):
                    self.RETURNDATASIZE = int2hex(hex2int(retlength) + hex2int("0x20"))

                if isinstance(addr, SymbolicValue):
                    if addr.annotation == "CALLDATALOAD":
                        if addr.uid not in self.call_list:
                            self.call_list.append(addr.uid)
                    if addr.taint == None:
                        taint = addr
                    else:
                        taint = addr.taint                    
                    memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN', taint)
                else:
                    if hex2int(addr) > 999999:
                        memory.memory[offset] = SymbolicValue('bitvec', 256, 'CALL_RETURN')
                    else:
                        self.error_occurred = True

                self._push(int2hex(1))
                self.close_dataload()

                if isinstance(addr, SymbolicValue) and addr.annotation == "CALLDATALOAD":
                    current_uid = addr.uid
                    if current_uid not in self.calldataload_list:
                        self.calldataload_list.append(current_uid)
                        add_dict(self.control_dict, current_uid)
                        add_dict(self.call_uidmap, current_uid)
                        self.call_order.append(current_uid)
                else:
                    if isinstance(length, str) and isinstance(addr, SymbolicValue):
                        if int(length, 16) != 0:
                            self.call_order.append(addr.uid)
                            if isinstance(argsoffset, str):
                                if int(int(length, 16) / 32) < 100:
                                    for i in range(int(int(length, 16) / 32)):
                                        try:
                                            cur_offset = int2hex(hex2int(argsoffset) + i * 32 + 4)
                                            temp_para = memory.memory[cur_offset]
                                            if addr.uid not in self.call_para:
                                                self.call_para[addr.uid] = list()
                                            if temp_para.uid not in self.call_para:
                                                self.call_para[addr.uid].append(temp_para.uid)
                                            if isinstance(temp_para, SymbolicValue):
                                                if int(length, 16) <= 40:
                                                    if temp_para.annotation == "CALLER":
                                                        self.check_caller = True
                                                    elif temp_para.taint != None and temp_para.taint.annotation == "CALLER":
                                                        self.check_caller = True
                                        except:
                                            pass                    

                if isinstance(length, str) and isinstance(addr, SymbolicValue):
                    if int(length, 16) != 0:
                        self.contract_map[addr.uid] = True

            elif opcode == "RETURNDATACOPY":
                for i in range(3):
                    self._pop()
                self.close_dataload()
            elif opcode == "EXP":
                base = self._pop()
                exponent = self._pop()

                # Ensure that base and exponent are valid for exponentiation operation.
                # If not, push a default symbolic value and return.
                if not (isinstance(base, (int, str)) and isinstance(exponent, (int, str))):
                    self._push(SYMBOLIC_default())
                    return

                try:
                    base_int = hex2int(base) if isinstance(base, str) else base
                    exponent_int = hex2int(exponent) if isinstance(exponent, str) else exponent

                    if base_int < 0 or exponent_int < 0:
                        #raise ValueError('Base or exponent is negative')
                        pass

                    # Use the `pow` function with a modulus argument to prevent overflow
                    # Choose a large modulus to preserve the result's accuracy
                    modulus = 2 ** 256
                    result = int2hex(pow(base_int, exponent_int, modulus))
                    result = cut_0x(result)
                    self._push(result)
                except Exception as e:
                    # Push a default symbolic value and print detailed error message for debugging
                    #print(f'Error during EXP operation: {str(e)}')
                    self._push(SymbolicValue('bitvec', 256, 'EXP'))
                    
            elif opcode == "NOT":
                a = self._pop()
                try:
                    result = int2hex(~hex2int(a) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
                    result = cut_0x(result)
                except:
                    result = SymbolicValue('bool', "NOT")
                self._push(result)
            elif opcode == "MOD":
                a = self._pop()
                b = self._pop()
                try:
                    self._push(int2hex(hex2int(a) % hex2int(b)))
                except:
                    self._push(SymbolicValue('bitvec', 256, 'MOD'))

            elif opcode == "SIGNEXTEND":
                a = self._pop()
                b = self._pop()
                try:
                    self._push(sign_extend(a, b))
                except:
                    self._push(SymbolicValue('bitvec', 256, 'SIGNEXTEND'))

            elif opcode == "CALLER":
                self._push(SymbolicValue('bitvec', 256, 'CALLER'))
                self.close_dataload()
            elif opcode == "ADDRESS":
                self._push(SymbolicValue('bitvec', 256, 'ADDRESS'))
                self.close_dataload()
            elif opcode == "RETURNDATASIZE":
                #size = int2hex(32)  # 返回数据大小为32个字节
                #self._push(size)
                if self.RETURNDATASIZE == None:
                    self._push(SymbolicValue('bitvec', 256, 'RETURNDATASIZE'))
                else:
                    self._push(self.RETURNDATASIZE)
                self.close_dataload()
            elif opcode == "CHAINID":
                self._push(SymbolicValue('bitvec', 256, 'CHAINID'))
                self.close_dataload()
            elif opcode == "TIMESTAMP":
                self._push(SymbolicValue('bitvec', 256, 'TIMESTAMP'))
                self.close_dataload()
            elif opcode == "BALANCE":
                self._push(SymbolicValue('bitvec', 256, 'BALANCE'))
                self.close_dataload()
            elif opcode == "SELFBALANCE":
                self._push(SymbolicValue('bitvec', 256, 'SELFBALANCE'))
                self.close_dataload()
            elif opcode == "CALLVALUE":
                self._push(SymbolicValue('bitvec', 256, 'CALLVALUE'))
            elif opcode == "NUMBER":
                self._push(SymbolicValue('bitvec', 256, 'NUMBER'))
                self.close_dataload()
            elif opcode == "COINBASE":
                self._push(SymbolicValue('bitvec', 256, 'COINBASE'))
                self.close_dataload()
            elif opcode == "BYTE":
                self._push(SymbolicValue('bitvec', 256, 'BYTE'))
                self.close_dataload()
            elif opcode == "DIFFICULTY":
                self._push(SymbolicValue('bitvec', 256, 'DIFFICULTY'))
                self.close_dataload()
            elif opcode == "ORIGIN":
                self._push(SymbolicValue('bitvec', 256, 'CALLER'))
                self.close_dataload()
            elif opcode == "CODESIZE":
                self._push(SymbolicValue('bitvec', 256, 'CODESIZE'))
                self.close_dataload()
            elif opcode == "EXTCODEHASH":
                addr = self._pop()
                result = SymbolicValue('bitvec', 256, 'EXTCODEHASH')
                if isinstance(addr, SymbolicValue):
                    if addr.annotation in ("CALLDATALOAD", "CALLER"):
                        result.get_taint(addr)
                    elif addr.taint != None and addr.taint.annotation in ("CALLDATALOAD", "CALLER"):
                        result.get_taint(addr.taint)
                self._push(result)
                self.close_dataload()
            elif opcode == "GASPRICE":
                self._push(SymbolicValue('bitvec', 256, 'GASPRICE'))
                self.close_dataload()         
            elif opcode == "CREATE2":
                for i in range(4):
                    self._pop()
                self._push(SymbolicValue('bitvec', 256, 'CREATE2'))
                self.close_dataload()       
            elif opcode == "CREATE":
                for i in range(3):
                    self._pop()
                self._push(SymbolicValue('bitvec', 256, 'CREATE'))
                self.close_dataload()           
            elif opcode == "BLOCKHASH":
                self._push(SymbolicValue('bitvec', 256, 'BLOCKHASH'))   
            elif opcode == "SELFDESTRUCT":
                self._pop()
                self.close_dataload()
            elif opcode in ("STOP", "RETURN"):
                pass
            # 添加其他opcode的执行逻辑
            elif opcode == 'MY_OPCODE':
                self._my_opcode()
            else:
                #raise ValueError("Invalid opcode: " + opcode)
                pass
        except (IndexError, ValueError) as e:
            #print(e)
            self.error_occurred = True

    # 其他辅助方法

    def _get_push_value(self, value):
        # 从opcode中提取要推送的值
        # 这里的实现取决于你的具体需求
        return value

    def _push(self, value):
        # 将值压入栈中
        self.stack.append(value)

    def _pop(self):
        # 从栈顶弹出一个值
        if len(self.stack) == 0:
            #raise IndexError("Stack underflow")
            pass
        return self.stack.pop()

    def _swap(self, n):
        # 将栈顶的值与第n个值进行交换
        if n >= len(self.stack):
            #raise IndexError("Invalid swap index")
            pass
        self.stack[-1], self.stack[-n-1] = self.stack[-n-1], self.stack[-1]

    def _dup(self, n):
        # 将第n个值复制并推送到栈中
        if n >= len(self.stack):
            #raise IndexError("Invalid duplicate index")
            pass
        self.stack.append(self.stack[-n])

    def _log(self, n):
        # 执行LOG操作
        # 这里的实现取决于你的具体需求
        if n < 0 or n > 4:
            #raise ValueError("Invalid log operation: n must be between 1 and 4.")  
            pass
        if len(self.stack) < n + 2:
            #raise IndexError("Stack underflow: Not enough elements for log operation.") 
            pass
        for i in range(n + 2):
            self._pop()

    def _my_opcode(self):
        # 执行自定义的opcode操作
        # 这里的实现取决于你的具体需求
        ...

class EVMStorage:
    def __init__(self):
        self.storage = {}

    def sload(self, offset):
        default = '0' * 32  # 默认值为32个字节的全零字符串
        value = self.storage.get(offset, default)
        return value

    def sstore(self, offset, value):
        self.storage[offset] = value


class EVMMemory:
    def __init__(self):
        self.memory = {}
        self.sha3_list = []

    def mload(self, offset):
        default = SymbolicValue('bitvec', 256, 'mload')
        value = self.memory.get(offset, default)
        return value

    def mstore(self, offset, value):
        self.memory[offset] = value

def cut_0x(num_str):
    if len(num_str) > 66:
        res = "0x" + num_str[-64:]
    else:
        res = num_str
    return res

def copy_taint(a, b, address_list, res, check_address_list = True):
    # Use helper function to reduce code repetition
    def handle_symbolic(value, address_list, res):
        if value.taint is not None:
            res.get_taint(value.taint)
        elif value.annotation == "CALLER":
            res.get_taint(value)
        elif value.annotation == "CALLDATALOAD" and check_address_list and value.uid in address_list:
            res.get_taint(value)
        elif value.annotation == "CALLDATALOAD" and not check_address_list:
            res.get_taint(value)
        elif value.annotation == "SLOAD":
            res.get_taint(value)
        try:
            res.sload_taint = deepcopy(value.sload_taint)
        except:
            pass

    if isinstance(a, SymbolicValue):
        handle_symbolic(a, address_list, res)
    if isinstance(b, SymbolicValue):
        handle_symbolic(b, address_list, res)

    return res

def int2hex(num):
    if num == 0:
        return "0x00"
    else:
        return hex(num)

def hex2int(num):
    return int(num, 16)

def int2signed(value):
    max_int = 2**(32 - 1)
    return value if value < max_int else value - 2**32

def signed_div(a, b):
    a_signed = int2signed(hex2int(a))
    b_signed = int2signed(hex2int(b))
    result = a_signed // b_signed if b_signed != 0 else 0
    return int2hex(result)

def signed_less_than(a, b):
    return int2hex(1) if a < b else int2hex(0)

def is_symbolic_default(variable):
    return isinstance(variable, SYMBOLIC_default)

def compare_with_annotation(value, annotation):
    if is_symbolic_default(value):
        return value.annotation == annotation
    else:
        return value == annotation

def add_dict(mydict, value):
    dict_length = len(mydict)
    mydict[dict_length] = value

def sign_extend(a, b):
    a_int = hex2int(a)
    b_int = hex2int(b)
    if a_int < 32 and b_int != 0:
        mask = 1 << (8 * a_int - 1)
        if b_int & mask:
            result = b_int | ~(mask - 1)
        else:
            result = b_int & (mask - 1)
        return int2hex(result)
    return b