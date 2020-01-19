from pathlib import Path
from tokenizer import Flix
from parser import Taurus
from semiotics import Pilgrim
import sys


class Malcolm:
    """
    """

    # pc = program counter
    pc = 7

    # mp = "memory pointer" points
    # to top of memory (for temp storage)
    mp = 6

    # gp = "global pointer" points
    # to bottom of memory for (global )
    # variable storage
    gp = 5

    # accumulator
    ac = 0

    # 2nd accumulator
    ac1 = 1

    semantic_error_at = 'Cannot proceed with code generation. There are still semantic errors at'
    bug_emit = 'BUG in emitBackup'
    output_dir = Path('middle')

    def __init__(self, semiotics):
        """
        """
        self.root = None
        self.semiotics = semiotics
        self.prru_code = []
        self.symbol_table = self.semiotics.symbol_table
        self._break = False
        self._break_loc = -1

        # TraceCode = True causes comments to be written
        # to the PM code file as code is generated
        self.TraceCode = True

        # PM location number for current instruction emission
        self.pulga = 0  # emitLoc

        # Highest PM location emitted so far. For use in conjunction with emitSkip, emitBackup, and emitRestore
        self.highEmitLoc = 0  # gran danés

        # tmpOffset is the memory offset for temps It is decremented each time a temp is stored, and incremeted when loaded again
        self.tmpOffset = 0

    def degen(self):
        """
        """
        self.prru_code.clear()

        self._break_loc = -1

        self.pulga = 0
        self.highEmitLoc = 0
        self.tmpOffset = 0

        self.semiotics.walk()
        if self.semiotics.errors:
            msg = f'{self.semantic_error_at} {self.semiotics.errors[0].split(" ")[2]}'
            raise RuntimeError(msg)
        self.root = self.semiotics.root

        self.emit_comment('Standard prelude:')
        self.emit_rm('LD', self.mp, 0, self.ac, 'load maxaddress from location 0')
        self.emit_rm('ST', self.ac, 0, self.ac, 'clear location 0')
        self.emit_comment('End of standard prelude')

        if len(self.root.children) == 1 and self.root.children[0].lexeme == self.semiotics.parser.sl_label:
            temp = self.root.children[0]
            self.gent_stmt(temp)
        elif len(self.root.children) == 2:
            temp = self.root.children[1]
            self.gent_stmt(temp)

        self.emit_comment('End of execution')
        self.emit_ro('HALT', 0, 0, 0, '')

    def write_output(self, prru_code_filename='prru_code.txt'):
        """
        """
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.degen()
        with (self.output_dir / prru_code_filename).open('w', encoding='utf-8') as prru_code_file:
            for _ in self.prru_code:
                prru_code_file.write(f'{_}\n')

    def _dir_in_tabledance(self, atom):
        if atom.lexeme.startswith(self.semiotics.parser.assignment_label) or atom.lexeme.startswith('cin:'):
            lexeme = atom.lexeme.split()[-1]
        else:
            lexeme = atom.lexeme
        return self.symbol_table[lexeme].mem_location

    def update_high(self):
        if self.highEmitLoc < self.pulga:
            self.highEmitLoc = self.pulga

    def emit_comment(self, c):
        """
        Procedure emit_comment prints a comment line
        with comment c in the code file
        :param c: comment
        """
        if self.TraceCode:
            self.prru_code.append(f'* {c}')

    def emit_ro(self, op, r, s, t, c):
        """
        Procedure emit_ro emits a register-only PM instruction

        :param op: the opcode
        :param r: target register
        :param s: 1st source register
        :param t: 2nd source register
        :param c: a comment to be printed if TraceCode is TRUE
        """
        if self.TraceCode:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{s},{t}\t{c}')
        else:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{s},{t}')
        self.pulga += 1
        self.update_high()

    def emit_rm(self, op, r, d, s, c):
        """
        Procedure emit_rm emits a register-to-memory PM instruction

        :param op: the opcode
        :param r: target register
        :param d: the offset
        :param s: the base register
        :param c: a comment to be printed if TraceCode is TRUE
        """
        if self.TraceCode:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{d}({s})\t{c}')
        else:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{d}({s})')
        self.pulga += 1
        self.update_high()

    # Skipper
    def emit_skip(self, how_many):
        """
        Function emit_skip skips "howMany" code locations for later backpatch.
        It also returns the current code position

        :param how_many: locations to skip
        :return: The current code position
        """
        i = self.pulga
        self.pulga += how_many
        self.update_high()
        return i

    # Cabo
    def emit_backup(self, loc):
        """
        Procedure emit_backup backs up to loc
        :param loc: a previously skipped location
        """
        if loc > self.highEmitLoc:
            raise RuntimeError(self.bug_emit)
        self.pulga = loc

    # Kowalski
    def emit_restore(self):
        """
        Procedure emit_restore restores the current code position to the highest previously unemitted position
        """
        self.pulga = self.highEmitLoc

    # Rico
    def emit_rm_abs(self, op, r, a, c):
        """
        Procedure emit_rm_abs converts an absolute reference
        to a pc-relative reference when emitting a
        register-to-memory PM instruction

        :param op: the opcode
        :param r: target register
        :param a: the absolute location in memory
        :param c: a comment to be printed if TraceCode is TRUE
        """
        if self.TraceCode:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{a-(self.pulga+1)}({self.pc})\t{c}')
        else:
            self.prru_code.append(f'{self.pulga}:  {op}  {r},{a-(self.pulga+1)}({self.pc})')
        self.pulga += 1
        self.update_high()

    def gent_stmt(self, atom):
        """
        Procedure gen_stmt generates code at a statement node
        :param atom: current atom
        """
        for atom in atom.children:
            if atom.lexeme == 'if':
                self._gen_if(atom)
            elif atom.lexeme == 'while':
                self._gen_bruce_while(atom)
            elif atom.lexeme == 'repeat':
                self._gen_repeat(atom)
            elif atom.lexeme.startswith('cin'):
                self._gen_cin(atom)
            elif atom.lexeme == 'cout':
                self._gen_cout(atom)
            elif atom.lexeme == 'coutln':
                self._gen_coutln(atom)
            elif atom.lexeme == self.semiotics.parser.sl_label:
                self.gent_stmt(atom)
            elif atom.lexeme.startswith(self.semiotics.parser.assignment_label):
                self._gen_assignment(atom)
            elif atom.lexeme == 'rompe':
                self._gen_break()

    def _gen_if(self, atom):
        if self.TraceCode:
            self.emit_comment('-> if')

        self.gen_exp(atom.children[0])

        loc2 = 0

        loc1 = self.emit_skip(1)
        self.emit_comment('if: jump after then belongs here')

        self.gent_stmt(atom.children[1])

        if len(atom.children) == 3:
            loc2 = self.emit_skip(1)
            self.emit_comment('if: jump after else belongs here')

        current_loc = self.emit_skip(0)
        self.emit_backup(loc1)
        self.emit_rm_abs('JEQ', self.ac, current_loc, 'if: jmp to after then')
        self.emit_restore()

        if len(atom.children) == 3:
            self.gent_stmt(atom.children[2])
            current_loc = self.emit_skip(0)
            self.emit_backup(loc2)
            self.emit_rm_abs('LDA', self.pc, current_loc, 'jmp to after else')
            self.emit_restore()

        if self.TraceCode:
            self.emit_comment('<- if')

    def _gen_bruce_while(self, atom):
        if self.TraceCode:
            self.emit_comment('-> while')

        loc1 = self.emit_skip(0)
        self.gen_exp(atom.children[0])
        loc2 = self.emit_skip(1)
        self.gent_stmt(atom.children[1])

        current_loc = self.emit_skip(0)
        self.emit_backup(loc2)
        self.emit_rm_abs('JEQ', self.ac, current_loc + 1, 'jmp to after while')

        if self._break:
            self.emit_backup(self._break_loc)
            self.emit_rm_abs('LDA', self.pc, current_loc + 1, 'rompe jump')
            self._break = False

        self.emit_restore()
        self.emit_rm_abs('LDA', self.pc, loc1, 'jmp to expression')

        if self.TraceCode:
            self.emit_comment('<- while')

    def _gen_repeat(self, atom):
        if self.TraceCode:
            self.emit_comment('-> repeat')

        loc1 = self.emit_skip(0)
        self.gent_stmt(atom.children[0])
        self.gen_exp(atom.children[1])

        if self._break:
            loc2 = self.emit_skip(0)
            self.emit_backup(self._break_loc)
            self.emit_rm_abs('LDA', self.pc, loc2 + 1, 'rompe jump')
            self.emit_restore()
            self._break = False

        self.emit_rm_abs('JEQ', self.ac, loc1, 'repeat: jmp back to body')

        if self.TraceCode:
            self.emit_comment('<- repeat')

    def _gen_cin(self, atom):
        self.emit_ro('IN', self.ac, 0, 0, '-> read')
        loc = self._dir_in_tabledance(atom)
        self.emit_rm('ST', self.ac, loc, self.gp, '<- read')

    def _gen_cout(self, atom):
        self.gen_exp(atom.children[0])
        self.emit_ro('OUT', self.ac, 0, 0, '-> write')

    def _gen_coutln(self, atom):
        self.gen_exp(atom.children[0])
        self.emit_ro('OUTLN', self.ac, 0, 0, '-> write')

    def _gen_assignment(self, atom):
        if self.TraceCode:
            self.emit_comment('-> assignment')

        self.gen_exp(atom.children[0])
        loc = self._dir_in_tabledance(atom)
        self.emit_rm('ST', self.ac, loc, self.gp, 'assignment: store value')

        if self.TraceCode:
            self.emit_comment('<- assignment')

    def _gen_break(self):
        self._break = True
        self._break_loc = self.emit_skip(1)

    def gen_exp(self, atom):
        """
        Procedure gen_exp generates code at an expression node
        :param atom: current atom
        """
        if atom.category in (self.semiotics.parser.tokenizer.int_label, self.semiotics.parser.tokenizer.real_label,
                             self.semiotics.parser.tokenizer.boolean_label):
            if self.TraceCode:
                self.emit_comment("-> Const")
            if atom.lexeme == 'True':
                atom.lexeme = '1'
            elif atom.lexeme == 'False':
                atom.lexeme = '0'
            self.emit_rm('LDC', self.ac, atom.lexeme, 0, 'Load const')
            if self.TraceCode:
                self.emit_comment("<- Const")
        elif atom.category == self.semiotics.parser.tokenizer.id_label:
            if self.TraceCode:
                self.emit_comment("-> Id")

            loc = self._dir_in_tabledance(atom)
            self.emit_rm('LD', self.ac, loc, self.gp, 'Load ID value')

            if self.TraceCode:
                self.emit_comment("<- Id")
        elif atom.lexeme in ('<', '<=', '>', '>=', '==', '!=', '+', '-', '*', '/'):
            if self.TraceCode:
                self.emit_comment('-> Op')

            if len(atom.children) == 2:
                self.gen_exp(atom.children[0])

                self.emit_rm('ST', self.ac, self.tmpOffset, self.mp, 'op: push left operand')
                self.tmpOffset -= 1

                self.gen_exp(atom.children[1])

                self.tmpOffset += 1
                self.emit_rm('LD', self.ac1, self.tmpOffset, self.mp, 'op: load left operand')

                if atom.lexeme == '+':
                    self.emit_ro('ADD', self.ac, self.ac1, self.ac, 'op +')
                elif atom.lexeme == '-':
                    self.emit_ro('SUB', self.ac, self.ac1, self.ac, 'op -')
                elif atom.lexeme == '*':
                    self.emit_ro('MUL', self.ac, self.ac1, self.ac, 'op *')
                elif atom.lexeme == '/':
                    self.emit_ro('DIV', self.ac, self.ac1, self.ac, 'op /')
                elif atom.lexeme == '<':
                    self._gen_cmp('JLT', atom.lexeme)
                elif atom.lexeme == '<=':
                    self._gen_cmp('JLE', atom.lexeme)
                elif atom.lexeme == '>':
                    self._gen_cmp('JGT', atom.lexeme)
                elif atom.lexeme == '>=':
                    self._gen_cmp('JGE', atom.lexeme)
                elif atom.lexeme == '==':
                    self._gen_cmp('JEQ', atom.lexeme)
                elif atom.lexeme == '!=':
                    self._gen_cmp('JNE', atom.lexeme)
            elif len(atom.children) == 1:
                self.emit_rm('LDC', self.ac, 0, self.ac, 'load 0 in ac for sign operatios')

                self.emit_rm('ST', self.ac, self.tmpOffset, self.mp, 'op: push left operand')
                self.tmpOffset -= 1

                self.gen_exp(atom.children[0])

                self.tmpOffset += 1
                self.emit_rm('LD', self.ac1, self.tmpOffset, self.mp, 'op: load left operand')

                if atom.lexeme == '+':
                    self.emit_ro('ADD', self.ac, self.ac1, self.ac, 'op +')
                elif atom.lexeme == '-':
                    self.emit_ro('SUB', self.ac, self.ac1, self.ac, 'op -')

            if self.TraceCode:
                self.emit_comment('<- Op')

    def _gen_cmp(self, opcode, operator):
        self.emit_ro('SUB', self.ac, self.ac1, self.ac, f'op {operator}')
        self.emit_rm(opcode, self.ac, 2, self.pc, 'br if true')
        self.emit_rm('LDC', self.ac, 0, self.ac, 'false case')
        self.emit_rm('LDA', self.pc, 1, self.pc, 'unconditional jump')
        self.emit_rm('LDC', self.ac, 1, self.ac, 'true case')

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'root={self.root!r}',
                f'prru_code={self.prru_code!r}',
                f'output_dir={self.output_dir!r}']
        return f'{classname}({", ".join(args)})'


if __name__ == '__main__':
    Malcolm(Pilgrim(Taurus(Flix(sys.argv[1])))).write_output()
