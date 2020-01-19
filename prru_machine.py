from tokenizer import Flix
from parser import Taurus
from semiotics import Pilgrim
from prru_code import Malcolm
from pathlib import Path
from enum import Enum
import sys


class Instruction:
    """"""
    __slots__ = ('iop', 'iarg1', 'iarg2', 'iarg3')

    def __init__(self, iop='HALT', iarg1=0, iarg2=0, iarg3=0):
        """
        """
        self.iop = iop
        self.iarg1 = iarg1
        self.iarg2 = iarg2
        self.iarg3 = iarg3

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'{self.iop!r}', f'{self.iarg1!r}', f'{self.iarg2!r}', f'{self.iarg3!r}']
        return f'{classname}({", ".join(args)})'


class StepResult(Enum):
    srOKAY = 1
    srHALT = 2


class Sigma:
    """
    """
    bad_location = 'Bad location'
    location_too_large = 'Location too large'
    missing_colon = 'Missing colon'
    missing_opcode = 'Missing opcode'
    illegal_opcode = 'Illegal opcode'
    bad_first = 'Bad first register'
    bad_second = 'Bad second register'
    bad_third = 'Bad third register'
    bad_displacement = 'Bad displacement'

    invalid_conversion_label = 'Invalid conversion to'
    division_by_zero_label = 'Division by zero'
    dmem_out_of_range_label = 'Memory index out of range'
    imem_out_of_range_label = 'Instruction memory index out of range'

    output_dir = Path('Runtime')

    iaddr_size = 1024
    daddr_size = 1024
    no_regs = 8
    pc_reg = 7

    RR_instructions = (
        'HALT',  # halt, operands are ignored
        'IN',  # read into reg(r); s and t are ignored
        'OUT',  # write from reg(r), s and t are ignored
        'OUTLN',  # write from reg(r) with line ending, s and t are ignored
        'ADD',  # reg(r) = reg(s)+reg(t)
        'SUB',  # reg(r) = reg(s)-reg(t)
        'MUL',  # reg(r) = reg(s)*reg(t)
        'DIV'  # reg(r) = reg(s)/reg(t)
    )

    RM_instructions = (
        'LD',  # reg(r) = mem(d+reg(s))
        'ST'  # mem(d+reg(s)) = reg(r)
    )

    RA_instructions = (
        'LDA',  # reg(r) = d+reg(s)
        'LDC',  # reg(r) = d ; reg(s) is ignored
        'JLT',  # if reg(r)<0 then reg(7) = d+reg(s)
        'JLE',  # if reg(r)<=0 then reg(7) = d+reg(s)
        'JGT',  # if reg(r) > 0 then reg(7) = d + reg(s)
        'JGE',  # if reg(r) >= 0 then reg(7) = d + reg(s)
        'JEQ',  # if reg(r) == 0 then reg(7) = d + reg(s)
        'JNE'  # if reg(r)!=0 then reg(7) = d+reg(s)
    )

    def __init__(self, malcolm):
        """
        """
        self.prru_code = None
        self._symbol_table = {}
        self.malcolm = malcolm

        self.iloc = 0
        self.dloc = 0
        self.traceflag = False
        self.icountflag = False
        self.iMem = {}
        self.dMem = {}
        self.reg = [0] * self.no_regs
        self.done = False

    def evaluate(self):
        """
        """
        self.malcolm.degen()
        self.prru_code = self.malcolm.prru_code
        self._symbol_table = self.malcolm.symbol_table
        self._clear_symtab_values()
        self._read_prru_code()

        # print('TM  simulation (enter h for help)...\n')

        while not self.done:
            self.done = not self.do_command()

    def write_output(self, sym_tab_filename='symtab.txt'):
        """
        :param sym_tab_filename: File to write the symbol table into. Default: symtab.txt.
        """
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.evaluate()
        with (self.output_dir / sym_tab_filename).open('w', encoding='utf-8') as sym_tab_file:
            for key, value in self._symbol_table.items():
                sym_tab_file.write(f'{key}: {value}\n')

    def _read_prru_code(self):
        self.reg = [0] * self.no_regs
        self.dMem.clear()
        self.dMem[0] = self.daddr_size - 1
        self.iMem = {}

        line_no = 0

        iarg1 = 0
        iarg2 = 0
        iarg3 = 0

        for line in self.prru_code:
            line_no += 1
            if line[0] != '*':
                if ':' not in line:
                    raise RuntimeError(f'{self.missing_colon} at {line_no}')

                temp = line.split('  ')
                loc = int(temp[0].split(':')[0])
                opcode = temp[1]
                regs = temp[2].split('\t')[0]

                if not isinstance(loc, int):
                    raise RuntimeError(f'{self.bad_location} at {line_no}')
                if loc > self.iaddr_size:
                    raise RuntimeError(f'{self.location_too_large} at {line_no}, instruction {loc}')
                if not opcode:
                    raise RuntimeError(f'{self.missing_opcode} at {line_no}, instruction {loc}')
                if opcode not in self.RR_instructions + self.RM_instructions + self.RA_instructions:
                    raise RuntimeError(f'{self.illegal_opcode}')

                if opcode in self.RR_instructions:
                    regs = regs.split(',')
                    iarg1 = int(regs[0])
                    iarg2 = int(regs[1])
                    iarg3 = int(regs[2])
                    if not isinstance(iarg1, int):
                        raise RuntimeError(f'{self.bad_first} at {line_no}, instruction {loc}')
                    if not isinstance(iarg2, int):
                        raise RuntimeError(f'{self.bad_second} at {line_no}, instruction {loc}')
                    if not isinstance(iarg3, int):
                        raise RuntimeError(f'{self.bad_third} at {line_no}, instruction {loc}')
                elif opcode in self.RM_instructions + self.RA_instructions:
                    temp = regs.split(',')
                    iarg1 = int(temp[0])
                    temp2 = temp[1].split('(')
                    iarg2 = self._str_to_lit(temp2[0])
                    iarg3 = int(temp2[1].split(')')[0])

                    if not isinstance(iarg1, int):
                        raise RuntimeError(f'{self.bad_first} at {line_no}, instruction {loc}')
                    if not isinstance(iarg2, float) and not isinstance(iarg2, int):
                        raise RuntimeError(f'{self.bad_displacement} at {line_no}, instruction {loc}')
                    if not isinstance(iarg3, int):
                        raise RuntimeError(f'{self.bad_second} at {line_no}, instruction {loc}')

                self.iMem[loc] = Instruction(opcode, iarg1, iarg2, iarg3)

    def step_pm(self):
        r = 0
        s = 0
        t = 0
        m = 0
        pc = self.reg[self.pc_reg]

        if pc < 0 or pc > self.iaddr_size:
            raise RuntimeError(self.imem_out_of_range_label)

        self.reg[self.pc_reg] = pc + 1

        curr_inst = self.iMem[pc]
        if curr_inst.iop in self.RR_instructions:
            r = curr_inst.iarg1
            s = curr_inst.iarg2
            t = curr_inst.iarg3
        elif curr_inst.iop in self.RM_instructions:
            r = curr_inst.iarg1
            s = curr_inst.iarg3
            m = int(curr_inst.iarg2 + self.reg[s])
            if m < 0 or m > self.daddr_size:
                raise RuntimeError(self.dmem_out_of_range_label)
        elif curr_inst.iop in self.RA_instructions:
            r = curr_inst.iarg1
            s = curr_inst.iarg3
            m = int(curr_inst.iarg2 + self.reg[s])

        if curr_inst.iop == 'HALT':
            # print(f'{curr_inst.iop}: {r},{s},{t}')
            return StepResult.srHALT
        elif curr_inst.iop == 'IN':
            self.reg[r] = input('🐶> ')
        elif curr_inst.iop == 'OUT':
            print(self.reg[r], end='')
        elif curr_inst.iop == 'OUTLN':
            print(self.reg[r])
        elif curr_inst.iop == 'ADD':
            self.reg[r] = self.reg[s] + self.reg[t]
        elif curr_inst.iop == 'SUB':
            self.reg[r] = self.reg[s] - self.reg[t]
        elif curr_inst.iop == 'MUL':
            self.reg[r] = self.reg[s] * self.reg[t]
        elif curr_inst.iop == 'DIV':
            if self.reg[t] != 0:
                if isinstance(self.reg[s], int) and isinstance(self.reg[t], int):
                    self.reg[r] = int(self.reg[s] / self.reg[t])
                else:
                    self.reg[r] = self.reg[s] / self.reg[t]
            else:
                raise RuntimeError(self.division_by_zero_label)
        elif curr_inst.iop == 'LD':
            self.reg[r] = self.dMem[m]
        elif curr_inst.iop == 'ST':
            typex = self._typex_in_tabledance(m)
            if typex:
                self.dMem[m] = self._put_value(self.reg[r], typex)
                self._update_tabledance(m, self.reg[r])
            else:
                self.dMem[m] = self.reg[r]
        elif curr_inst.iop == 'LDA':
            self.reg[r] = m
        elif curr_inst.iop == 'LDC':
            self.reg[r] = curr_inst.iarg2
        elif curr_inst.iop == 'JLT':
            if self.reg[r] < 0:
                self.reg[self.pc_reg] = m
        elif curr_inst.iop == 'JLE':
            if self.reg[r] <= 0:
                self.reg[self.pc_reg] = m
        elif curr_inst.iop == 'JGT':
            if self.reg[r] > 0:
                self.reg[self.pc_reg] = m
        elif curr_inst.iop == 'JGE':
            if self.reg[r] >= 0:
                self.reg[self.pc_reg] = m
        elif curr_inst.iop == 'JEQ':
            if self.reg[r] == 0:
                self.reg[self.pc_reg] = m
        elif curr_inst.iop == 'JNE':
            if self.reg[r] != 0:
                self.reg[self.pc_reg] = m
        return StepResult.srOKAY

    def do_command(self):
        stepcnt = 0
        command = ''
        while not command:
            command = input('\nEnter command: ')
        cmd = command[0]

        if cmd == 'h':
            print('\nCommands are: ')
            print('   g(o        Execute TM instructions until HALT')
            print('   c(lear     Reset simulator for new execution of program')
            print('   h(elp      Cause this list of commands to be printed')
            print('   q(uit      Terminate the simulation')
        elif cmd == 'g':
            stepcnt = 1
        elif cmd == 'c':
            self.iloc = 0
            self.dloc = 0
            stepcnt = 0
            self.reg = [0] * self.no_regs
            self.dMem.clear()
            self.dMem[0] = self.daddr_size - 1
        elif cmd == 'q':
            return False
        else:
            print(f'Command {cmd} unkown')

        step_result = StepResult.srOKAY
        if stepcnt > 0:
            if cmd == 'g':
                stepcnt = 0
                while step_result == StepResult.srOKAY:
                    self.iloc = self.reg[self.pc_reg]
                    # if self.traceflag:
                    # self.write_instruction(self.iloc)
                    step_result = self.step_pm()
                    stepcnt += 1
                if self.icountflag:
                    print(f'Number of instructions executed = {stepcnt}')
            else:
                while stepcnt > 0 and step_result == StepResult.srOKAY:
                    self.iloc = self.reg[self.pc_reg]
                    # if self.traceflag:
                    # self.write_instruction(self.iloc)
                    step_result = self.step_pm()
                    stepcnt -= 1
        # print stepresult
        return True

    def _clear_symtab_values(self):
        for identifier, info in self._symbol_table.items():
            if info.typex == 'int':
                info.val = 0
            elif info.typex == 'real':
                info.val = 0.0
            elif info.typex == 'boolean':
                info.val = False

    def _put_value(self, val, typex):
        try:
            if val == 'True':
                val = True
            elif val == 'False':
                val = False

            if typex == 'int':
                return int(val)
            elif typex == 'real':
                return float(val)
            elif typex == 'boolean':
                return bool(float(val))
        except ValueError:
            raise RuntimeError(f'{self.invalid_conversion_label} {typex}')

    @staticmethod
    def _str_to_lit(string):
        if string == 'True':
            return True
        elif string == 'False':
            return False
        else:
            try:
                return int(string)
            except ValueError:
                return float(string)

    def _typex_in_tabledance(self, mem_loc):
        for _id, info in self._symbol_table.items():
            if info.mem_location == mem_loc:
                return info.typex

    def _update_tabledance(self, mem_loc, value):
        for _id, info in self._symbol_table.items():
            if info.mem_location == mem_loc:
                info.val = value

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'reg={self.reg!r}']
        return f'{classname}({", ".join(args)})'


if __name__ == '__main__':
    Sigma(Malcolm(Pilgrim(Taurus(Flix(sys.argv[1]))))).write_output()
