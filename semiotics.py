"""Semantic analyzer for the "Tiny-Extended" programming language.

Grammar Rule                                Semantic Rules


This module exports:
  - IdInfo     class containing the memory location, source code location, value and type of a variable.
  - Pilgrim    class that converts a syntax tree into an evaluated syntax tree.
"""
from anytree import RenderTree, PreOrderIter, PostOrderIter
from dotexport import RenderTreeGraph
from tokenizer import Flix
from parser import Taurus
from pathlib import Path
import sys
import re


class IdInfo:
    """Class containing the memory location, source code location, value and type of an identifier."""
    __slots__ = ('mem_location', 'location', 'val', 'typex')

    def __init__(self, atom, mem_location):
        """An instance of IdInfo.

        :param atom: The atom representing the identifier.
        :param mem_location: The identifier memory location.
        """
        self.mem_location = mem_location
        self.location = [atom.location]
        self.typex = atom.typex
        if self.typex == 'int':
            self.val = 0
        elif self.typex == 'real':
            self.val = 0.0
        elif self.typex == 'boolean':
            self.val = False

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'{self.mem_location!r}', f'{self.location!r}', f'{self.val!r}', f'{self.typex!r}']
        return f'{classname}({", ".join(args)})'

    def __str__(self):
        args = [f'{self.mem_location}', f'{self.location}', f'{self.val}', f'{self.typex}']
        return f'{"#".join(args)}'


class Pilgrim:
    """Convert a syntax tree into an evaluated syntax tree.

        Output can be customized by subclassing and redefining the following:
          - syntax_error_at           Label preceding the location of a syntax error before aborting semantic analysis.
          - already_declared_label    Message shown when an identifier is declared more than once.
          - warning_at_label          Label preceding the found warning location in a warning message.
          - error_at_label            Label preceding the found error location in an error message.
          - division_by_zero_label    Message shown when a division by zero is found.
          - expected_type_label       Label preceding the expected type in a type mismatch message.
          - not_declared_label        Message shown when an identifier is not found on the symbol table.
          - output_dir                Output directory.

        Instance variables:
          - root            The root of the evaluated syntax tree.
          - errors          A list of the found semantic errors.
          - parser          An instance of Taurus.

        Public methods:
          - walk            Iterate over the input tree and build the evaluated syntax tree according to the semantic rules.
          - write_output    Write the evaluated syntax tree.
    """

    syntax_error_at = 'Cannot proceed with semantic analysis. There are still syntax errors at'
    already_declared_label = 'Variable was already declared'
    warning_at_label = 'Warning at'
    error_at_label = 'Error at'
    division_by_zero_label = 'Division by zero'
    expected_type_label = 'Expected type:'
    not_declared_label = 'Variable was not declared'
    output_dir = Path('eAST')

    def __init__(self, parser):
        """A Pilgrim object used for semantic analysis.

        :param parser: An instance of Taurus.
        """
        self.root = None
        self.errors = []
        self.parser = parser
        self.symbol_table = {}
        self._mem_location = -1

    def walk(self):
        """Iterate over the input tree and build the evaluated syntax tree according to the semantic rules."""
        self.errors.clear()
        self.symbol_table.clear()
        self._mem_location = -1
        self.parser.parse()
        if self.parser.errors:
            error_location = re.search(r'[0-9]+:[0-9]+', self.parser.errors[0])
            if error_location:
                msg = f'{self.syntax_error_at} {error_location.group(0)}'
            else:
                msg = f'{self.parser.errors[0]}'
            raise RuntimeError(msg)
        self.root = self.parser.root
        self._eval(self.root)

    def write_output(self, etree_filename='etree.txt', errors_filename='errors.txt', sym_tab_filename='symtab.txt',
                     render_file='', orientation='LR'):
        """Write the evaluated syntax tree and the found semantic errors to their respective specified files.

        :param etree_filename: File to write the evaluated tree into. Default: etree.txt.
        :param errors_filename: File to write the errors into. Default: errors.txt.
        :param sym_tab_filename: File to write the symbol table into. Default: symtab.txt.
        :param render_file: Graphviz required. File to render the tree into, if desired.\
                            Supported formats: http://www.graphviz.org/content/output-formats.
        :param orientation: Render the tree from top to bottom, from left to right, from bottom to top,\
                            or from right to left with TB, LR, BT, or RL. Default: LR.
        """
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.walk()
        with (self.output_dir / etree_filename).open('w', encoding='utf-8') as etree_file:
            for pre, _, atom in RenderTree(self.root):
                etree_file.write(f'{pre}{atom}\n')
        with (self.output_dir / errors_filename).open('w', encoding='utf-8') as errors_file:
            for _ in self.errors:
                errors_file.write(f'{_}\n')
        with (self.output_dir / sym_tab_filename).open('w', encoding='utf-8') as sym_tab_file:
            for key, value in self.symbol_table.items():
                sym_tab_file.write(f'{key}: {value}\n')
        if render_file:
            RenderTreeGraph(self.root, graph='strict graph', options=[f'rankdir={orientation};'],
                            nodenamefunc=lambda node: f'{node.lexeme}|{node.category}|{node.location}',
                            nodeattrfunc=lambda node: self._atom_attributes(node)
                            ).to_picture(self.output_dir / render_file)

    def _add_location(self, lexeme, location):
        if location not in self.symbol_table[lexeme].location:
            self.symbol_table[lexeme].location.append(location)

    def _add_error(self, msg):
        if msg not in self.errors:
            self.errors.append(msg)

    def _eval(self, atom):
        self._eval_type(atom.children[0])
        self._eval_value(atom.children[1])

    def _eval_type(self, atom):
        for atom in PreOrderIter(atom):
            if atom.category == self.parser.tokenizer.id_label:
                if atom.lexeme in self.symbol_table:
                    self._add_error(f'{self.error_at_label} {atom.location}: token -> {atom.category}, '
                                    f'{atom.lexeme}. {self.already_declared_label}.')
                else:
                    atom.typex = atom.parent.lexeme
                    self._mem_location += 1
                    self.symbol_table[atom.lexeme] = IdInfo(atom, self._mem_location)

    def _eval_value(self, atom):
        for atom in PostOrderIter(atom):
            if atom.category == self.parser.tokenizer.op_label:
                atom.val = self._eval_op(atom)
            elif atom.lexeme.startswith(self.parser.assignment_label):
                if self._check_in_tabledance(atom):
                    val = self._eval_id_num_op(atom.children[0])
                    typex = self.symbol_table[atom.lexeme.split()[-1]].typex
                    if typex == 'real':
                        atom.val = float(val)
                        self.symbol_table[atom.lexeme.split()[-1]].val = float(val)
                    elif self._eval_assignment(typex, val):
                        atom.val = val
                        self.symbol_table[atom.lexeme.split()[-1]].val = val
                    else:
                        self._add_error(f'{self.warning_at_label} {atom.children[0].location}. '
                                        f'{self.expected_type_label} {self.symbol_table[atom.lexeme.split()[-1]].typex}')
                    self._add_location(atom.lexeme.split()[-1], atom.location)
            elif atom.lexeme in ('if', 'while') and atom.children[0].lexeme not in frozenset({'<=', '<', '>', '>=', '==', '!='}):
                atom.children[0].val = self._eval_condition(atom.children[0])
            elif atom.lexeme == 'repeat' and atom.children[1].lexeme not in frozenset({'<=', '<', '>', '>=', '==', '!='}):
                atom.children[1].val = self._eval_condition(atom.children[1])
            elif atom.lexeme in ('cout', 'coutln') and atom.children[0].category in self.parser.tokenizer.id_label:
                atom.children[0].val = self._eval_id_num_op(atom.children[0])
            elif atom.lexeme.startswith('cin'):
                if self._check_in_tabledance(atom):
                    self._add_location(atom.lexeme.split()[-1], atom._id_location)

    @staticmethod
    def _eval_assignment(typex, val):
        if typex == 'int':
            return isinstance(val, int)
        elif typex == 'boolean':
            return isinstance(val, bool)

    def _eval_op(self, atom):
        if atom.lexeme == '+':
            if len(atom.children) == 1:
                return self._eval_id_num_op(atom.children[0])
            else:
                return self._eval_id_num_op(atom.children[0]) + self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '-':
            if len(atom.children) == 1:
                return - self._eval_id_num_op(atom.children[0])
            else:
                return self._eval_id_num_op(atom.children[0]) - self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '*':
            return self._eval_id_num_op(atom.children[0]) * self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '/':
            temp = self._eval_id_num_op(atom.children[0])
            temp2 = self._eval_id_num_op(atom.children[1])
            if temp2 == 0:
                self._add_error(f'{self.error_at_label} {atom.children[1].location}. {self.division_by_zero_label}')
                return float('inf')
            else:
                if isinstance(temp, int) and isinstance(temp2, int):
                    return int(temp / temp2)
                else:
                    return temp / temp2
        elif atom.lexeme == '<':
            return self._eval_id_num_op(atom.children[0]) < self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '<=':
            return self._eval_id_num_op(atom.children[0]) <= self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '>':
            return self._eval_id_num_op(atom.children[0]) > self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '>=':
            return self._eval_id_num_op(atom.children[0]) >= self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '==':
            return self._eval_id_num_op(atom.children[0]) == self._eval_id_num_op(atom.children[1])
        elif atom.lexeme == '!=':
            return self._eval_id_num_op(atom.children[0]) != self._eval_id_num_op(atom.children[1])

    def _eval_id_num_op(self, atom):
        if atom.category == self.parser.tokenizer.int_label:
            return int(atom.lexeme)
        elif atom.category == self.parser.tokenizer.real_label:
            return float(atom.lexeme)
        elif atom.category == self.parser.tokenizer.boolean_label:
            return True if atom.lexeme == 'True' else False
        elif atom.category in self.parser.tokenizer.id_label:
            if self._check_in_tabledance(atom):
                if not hasattr(atom, '_inc_dec'):
                    self._add_location(atom.lexeme, atom.location)
                return self.symbol_table[atom.lexeme].val
            else:
                return 0
        elif atom.category == self.parser.tokenizer.op_label:
            return self._eval_op(atom)

    def _eval_condition(self, atom):
        if atom.category == self.parser.tokenizer.int_label:
            return False if int(atom.lexeme) == 0 else True
        elif atom.category == self.parser.tokenizer.real_label:
            return False if float(atom.lexeme) == 0 else True
        elif atom.category == self.parser.tokenizer.boolean_label:
            return False if atom.lexeme == 'False' else True
        elif atom.category in self.parser.tokenizer.id_label:
            if self._check_in_tabledance(atom):
                if not hasattr(atom, '_inc_dec'):
                    self._add_location(atom.lexeme, atom.location)
                return False if self.symbol_table[atom.lexeme].val == 0 else True
            else:
                return False
        elif atom.category == self.parser.tokenizer.op_label:
            return True if self._eval_op(atom) else False

    def _check_in_tabledance(self, atom):
        if atom.lexeme.startswith(self.parser.assignment_label) or atom.lexeme.startswith('cin:'):
            lexeme = atom.lexeme.split()[-1]
        else:
            lexeme = atom.lexeme
        if lexeme in self.symbol_table:
            return True
        else:
            self._add_error(f'{self.error_at_label} {atom.location}: token -> {atom.category}, '
                            f'{lexeme}. {self.not_declared_label}.')
            return False

    @staticmethod
    def _atom_attributes(atom):
        attr = []
        for key, value in filter(lambda item: not item[0].startswith('_'), atom.__dict__.items()):
            attr.append(f'{key}={value}')
        label = f'label="{atom.lexeme} ({", ".join(attr)})"' if attr else f'label="{atom.lexeme}"'
        return f'shape=doublecircle {label}'

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'root={self.root!r}',
                f'errors={self.errors!r}',
                f'parser={self.parser!r}',
                f'symbol_table={self.symbol_table!r}',
                f'_mem_location={self._mem_location!r}',
                f'syntax_error_at={self.syntax_error_at!r}',
                f'already_declared_label={self.already_declared_label!r}',
                f'warning_at_label={self.warning_at_label!r}',
                f'error_at_label={self.error_at_label!r}',
                f'division_by_zero_label={self.division_by_zero_label!r}',
                f'expected_type_label={self.expected_type_label!r}',
                f'not_declared_label={self.not_declared_label!r}',
                f'output_dir={self.output_dir!r}']
        return f'{classname}({", ".join(args)})'


if __name__ == '__main__':
    Pilgrim(Taurus(Flix(sys.argv[1]))).write_output(render_file='etree.pdf')
