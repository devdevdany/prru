"""Syntactic analyzer for the "Tiny-Extended" programming language.

EBNF grammar:
    program                =    "main" "{" declaration-list statement-list "}"
    declaration-list       =    {declaration ";"}
    declaration            =    type variable-list
    type                   =    "int" | "real" | "boolean"
    variable-list          =    "ID" {"," "ID"}
    statement-list         =    {statement}
    statement              =    selection | iteration | repetition | cin-stmt | cout-stmt | coutln-stmt | block | assignment | pre
    selection              =    "if" "(" expression ")" "then" block ["else" block]
    iteration              =    "while" "(" expression ")" loop-block
    repetition             =    "repeat" loop-block "until" "(" expression ")" ";"
    cin-stmt               =    "cin" "ID" ";"
    cout-stmt              =    "cout" expression ";"
    coutln-stmt            =    "coutln" expression ";"
    block                  =    "{" statement-list "}"
    loop-block             =    "{" loop-statement-list "}"
    loop-statement-list    =    { statement | break-stmt }
    break-stmt             =    "rompe" ";"
    assignment             =    "ID" assignment-type ";"
    assignment-type        =    simple-assignment | post
    simple-assignment      =    ":=" expression
    post                   =    una-op
    pre                    =    una-op "ID" ";"
    una-op                 =    "++" | "--"
    expression             =    simple-expression [rel-op simple-expression]
    rel-op                 =    "<=" | "<" | ">" | ">=" | "==" | "!="
    simple-expression      =    term {add-op term}
    add-op                 =    "+" | "-"
    term                   =    superfactor {mul-op superfactor}
    mul-op                 =    "*" | "/"
    superfactor            =    [add-op] factor
    factor                 =    "(" expression ")" | "NUM" | "ID" | "True" | "False"

This module exports:
  - Atom      A tree node wrapping a Token.
  - Taurus    class that converts a sequence of tokens into an abstract syntax tree.
"""

from anytree import NodeMixin, RenderTree
from dotexport import RenderTreeGraph
from tokenizer import Flix, Token
from pathlib import Path
from copy import copy
import sys


class Atom(NodeMixin):
    """Tree node wrapping a Token.

      - token       An instance of Token.
      - parent      The parent of this node.
      - lexeme      The token's lexeme.
      - category    The token's category.
      - location    The token's location.

    NodeMixin is subclassed to extend this class to a tree node.
    """
    separator = '|'

    def __init__(self, token, lexeme='', parent=None, **kwargs):
        """A tree node wrapping a Token.

        :param token: An instance of Token.
        :param lexeme: An alternative lexeme for token.
        :param parent: The parent of this node.
        :param kwargs: Any keyword arguments.
        """
        self._token = copy(token)
        if lexeme:
            self.lexeme = lexeme
        self.parent = parent
        self.__dict__.update(kwargs)

    @property
    def token(self):
        return self._token

    @token.setter
    def token(self, value):
        self._token = copy(value)

    @property
    def lexeme(self):
        """Token's lexeme"""
        return self.token.lexeme

    @lexeme.setter
    def lexeme(self, value):
        self.token.lexeme = value

    @property
    def category(self):
        """Token's category"""
        return self.token.category

    @property
    def location(self):
        """Token's location"""
        return self.token.location

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'{self.token!r}', f'{self.separator.join(atom.lexeme for atom in self.path)!r}']
        for key, value in filter(lambda item: not item[0].startswith('_'), self.__dict__.items()):
            args.append(f'{key}={value!r}')
        return f'{classname}({", ".join(args)})'

    def __str__(self):
        classname = self.__class__.__name__
        args = [self.separator.join([''] + [f'{atom.lexeme}#{atom.location}' for atom in self.path]), self.category, self.location]
        for key, value in filter(lambda item: not item[0].startswith('_'), self.__dict__.items()):
            args.append(f'@{key}={value}')
        return f'{classname}({", ".join(args)})'


class Taurus:
    """Convert a sequence of tokens into an abstract syntax tree.

        Output can be customized by subclassing and redefining the following:
          - list_category         Label for the list category.
          - dl_label              Label for declaration lists.
          - sl_label              Label for statement lists.
          - decl_starter_label    Label used when a declaration starter is expected.
          - stmt_starter_label    Label used when a statement starter is expected.
          - indep_id_label        Label used when an independent id is expected.
          - expected_op_label     Label used when an operator is expected.
          - lexical_error_at      Label preceding the location of a lexical error before aborting parsing.
          - error_at_label        Label preceding the found error location in an error message.
          - expected_label        Label preceding the expected lexeme in an error message.
          - assignment_label      Label preceding an ID in an assignment statement, including pre and post increments.
          - error_before          Message shown when the source code ends before the final "}" of "main".
          - error_after           Message shown when there is code after the final "}" of "main".
          - output_dir            Output directory.

        Instance variables:
          - root         The root of the syntax tree.
          - errors       A list of the found syntax errors.
          - tokenizer    An instance of Flix.

        Public methods:
          - parse           Read the input tokens and build the syntax tree according to the grammar.
          - write_output    Write the AST and the found syntax errors to their respective specified files.
    """
    list_category = 'LIST'
    dl_label = '<dl>'
    sl_label = '<sl>'
    decl_starter_label = 'Declaration starter'
    stmt_starter_label = 'Statement starter'
    indep_id_label = 'Independent ID'
    expected_op_label = 'Arithmetic or relational OP'
    lexical_error_at = 'Cannot proceed with parsing. There are still invalid tokens at'
    error_at_label = 'Error at'
    expected_label = 'Expected:'
    assignment_label = 'Assign to:'
    error_before = 'Error: Code ends suddenly before closing \'main\' block'
    error_after = 'Error: There\'s code after closing \'main\' block'
    output_dir = Path('AST')

    _first_dl = frozenset({'int', 'real', 'boolean'})
    _first_una = frozenset({'++', '--'})
    _first_rel = frozenset({'<=', '<', '>', '>=', '==', '!='})
    _first_add = frozenset({'+', '-'})
    _first_mul = frozenset({'*', '/'})
    _first_at = frozenset({':='}) | _first_una
    _first_sl = frozenset({'if', 'while', 'repeat', 'cin', 'cout', 'coutln', '{'}) | _first_una
    _first_else = frozenset({'else'})
    _first_until = frozenset({'until'})
    _first_fact = frozenset({'(', 'True', 'False'})
    _first_exp = _first_add | _first_fact
    _follow_dl = _first_sl | frozenset({'}'})
    _first_break_stmt = frozenset({'rompe'})
    _first_loop_sl = _first_sl | _first_break_stmt
    _follow_fact = _first_mul | _first_rel | _first_add | frozenset({';', ')'})

    def __init__(self, tokenizer):
        """A Taurus object used for parsing.

        :param tokenizer: An instance of Flix.
        """
        self.root = None
        self.errors = []
        self.tokenizer = tokenizer
        self._tokens = None
        self._curr = None
        self._ID = (self.tokenizer.id_label,)
        self._NUM = (self.tokenizer.int_label, self.tokenizer.real_label)
        self._ID_NUM = self._ID + self._NUM

    def parse(self):
        """Read the input tokens and build the syntax tree according to the grammar."""
        self.errors.clear()
        self._tokens = self.tokenizer.scan()
        self._get_token()
        self.root = self._program()

    def write_output(self, tree_filename='tree.txt', errors_filename='errors.txt', render_file='', orientation='LR'):
        """Write the AST and the found syntax errors to their respective specified files.

        :param tree_filename: File to write the tree into. Default: tree.txt.
        :param errors_filename: File to write the errors into. Default: errors.txt.
        :param render_file: Graphviz required. File to render the tree into, if desired.\
                            Supported formats: http://www.graphviz.org/content/output-formats.
        :param orientation: Render the tree from top to bottom, from left to right, from bottom to top,\
                            or from right to left with TB, LR, BT, or RL. Default: LR.
        """
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.parse()
        with (self.output_dir / tree_filename).open('w', encoding='utf-8') as tree_file:
            for pre, _, atom in RenderTree(self.root):
                tree_file.write(f'{pre}{atom}\n')
        with (self.output_dir / errors_filename).open('w', encoding='utf-8') as errors_file:
            for _ in self.errors:
                errors_file.write(f'{_}\n')
        if render_file:
            RenderTreeGraph(self.root, graph='strict graph', options=[f'rankdir={orientation};'],
                            nodenamefunc=lambda node: f'{node.lexeme}|{node.category}|{node.location}',
                            nodeattrfunc=lambda node: f'shape=doublecircle label="{node.lexeme}"'
                            ).to_picture(self.output_dir / render_file)

    @staticmethod
    def _try_next(generator):
        try:
            current_token = next(generator)
        except StopIteration:
            current_token = Token('', '', '')
        return current_token

    def _get_token(self):
        self._curr = self._try_next(self._tokens)
        if self._curr.category == 'error':
            raise RuntimeError(f'{self.lexical_error_at} {self._curr.location}')

    def _lookahead(self, current_token):
        gen = self.tokenizer.scan()
        t = self._try_next(gen)
        while t.location and t.location != current_token.location:
            t = self._try_next(gen)
        else:
            return self._try_next(gen)

    def _sync(self, expected_lexeme, syncset=frozenset(), category_flag=()):
        if self._curr.lexeme == expected_lexeme or self._check_id_num(expected_lexeme):
            self._get_token()
            return True
        else:
            self._add_error(expected_lexeme)
            self._scanto(syncset, category_flag)
            return False

    def _check_id_num(self, category_flag):
        return self._curr.category in category_flag

    def _add_error(self, expected_lexeme):
        if self._curr.lexeme and (not self.errors or self._curr.location not in self.errors[-1]):
            if isinstance(expected_lexeme, tuple):
                expected_lexeme = ', '.join([_ for _ in expected_lexeme])
            self.errors.append(f'{self.error_at_label} {self._curr.location}: token -> {self._curr.category}, '
                               f'{self._curr.lexeme}. {self.expected_label} {expected_lexeme}')

    def _scanto(self, syncset, category_flag):
        while self._curr.lexeme and self._curr.lexeme not in syncset and not self._check_id_num(category_flag):
            self._get_token()

    def _check_for_starter(self, expected_starter, first_set, category_flag):
        if self._curr.lexeme not in first_set and not self._check_id_num(category_flag):
            self._sync(expected_starter, first_set, category_flag)

    def _program(self):
        main = Atom(self._curr, 'Ø')
        if self._sync('main', self._first_dl | self._first_sl, self._ID):
            main.lexeme = 'main'
        self._sync('{', self._first_dl | self._follow_dl, self._ID)

        self._declaration_list().parent = main
        self._statement_list().parent = main

        if not self._curr.lexeme:
            self.errors.append(self.error_before)
        elif self._sync('}') and self._curr.lexeme:
            self.errors.append(self.error_after)
        return main

    def _declaration_list(self):
        self._check_for_starter(f'{self.decl_starter_label}, {self.stmt_starter_label}', self._first_dl | self._follow_dl, self._ID)
        dl = Atom(Token(self.dl_label, self.list_category, self._curr.location))
        while self._curr.lexeme in self._first_dl:
            var_type = Atom(self._curr, parent=dl)
            self._get_token()
            self._variable_list(var_type)
            self._sync(';', self._first_dl | self._follow_dl, self._ID)
            self._check_for_starter(f'{self.decl_starter_label}, {self.stmt_starter_label}', self._first_dl | self._follow_dl, self._ID)
        return dl

    def _variable_list(self, var_type):
        temp = self._curr
        if self._sync(self._ID, frozenset({',', ';'}) | self._first_dl | self._follow_dl, self._ID):
            Atom(temp, parent=var_type)
        while self._curr.lexeme == ',' or self._independent_id():
            self._sync(',', frozenset({',', ';'}) | self._first_dl | self._follow_dl, self._ID)
            if self._independent_id():
                Atom(self._curr, parent=var_type)
                self._get_token()
            else:
                self._sync(self.indep_id_label, frozenset({',', ';'}) | self._first_dl | self._follow_dl, self._ID)

    def _statement_list(self, additional_syncset=frozenset()):
        self._check_for_starter(self.stmt_starter_label, self._follow_dl | additional_syncset, self._ID)
        sl = Atom(Token(self.sl_label, self.list_category, self._curr.location))
        first_set = self._first_loop_sl if 'rompe' in additional_syncset else self._first_sl
        while self._curr.lexeme in first_set or self._check_id_num(self._ID):
            if self._curr.lexeme == 'if':
                self._selection(additional_syncset).parent = sl
            elif self._curr.lexeme == 'while':
                self._iteration(additional_syncset).parent = sl
            elif self._curr.lexeme == 'repeat':
                self._repetition(additional_syncset).parent = sl
            elif self._curr.lexeme == 'cin':
                self._cin_stmt(additional_syncset).parent = sl
            elif self._curr.lexeme in ('cout', 'coutln'):
                self._cout_stmt(additional_syncset).parent = sl
            elif self._curr.lexeme == '{':
                self._block(additional_syncset).parent = sl
            elif self._curr.lexeme == 'rompe':
                self._break_stmt(additional_syncset).parent = sl
            elif self._check_id_num(self._ID):
                self._assignment(additional_syncset).parent = sl
            elif self._curr.lexeme in self._first_una:
                self._pre(additional_syncset).parent = sl
            self._check_for_starter(self.stmt_starter_label, self._follow_dl | additional_syncset, self._ID)
        return sl

    def _selection(self, additional_syncset):
        if_atom = Atom(self._curr)
        self._get_token()
        self._sync('(', self._first_exp | self._follow_dl | additional_syncset | self._first_else, self._ID_NUM)
        self._expression(additional_syncset | self._first_else, True).parent = if_atom
        self._sync(')', frozenset({'then'}) | self._follow_dl | additional_syncset | self._first_else, self._ID)
        self._sync('then', self._follow_dl | additional_syncset | self._first_else, self._ID)
        self._block(additional_syncset | self._first_else).parent = if_atom
        if self._curr.lexeme == 'else':
            self._get_token()
            self._block(additional_syncset).parent = if_atom
        return if_atom

    def _iteration(self, additional_syncset):
        while_atom = Atom(self._curr)
        self._get_token()
        self._sync('(', self._first_exp | self._follow_dl | additional_syncset | self._first_break_stmt, self._ID_NUM)
        self._expression(additional_syncset | self._first_break_stmt, True).parent = while_atom
        self._sync(')', self._follow_dl | additional_syncset | self._first_break_stmt, self._ID)
        self._block(additional_syncset | self._first_break_stmt).parent = while_atom
        return while_atom

    def _repetition(self, additional_syncset):
        repeat_atom = Atom(self._curr)
        self._get_token()
        self._block(additional_syncset | self._first_until | self._first_break_stmt).parent = repeat_atom
        self._sync('until', frozenset({'('}) | self._follow_dl | additional_syncset | self._first_break_stmt, self._ID)
        self._sync('(', self._first_exp | self._follow_dl | additional_syncset | self._first_break_stmt, self._ID_NUM)
        self._expression(additional_syncset | self._first_break_stmt, True).parent = repeat_atom
        self._sync(')', frozenset({';'}) | self._follow_dl | additional_syncset | self._first_break_stmt, self._ID)
        self._sync(';', self._follow_dl | additional_syncset | self._first_break_stmt, self._ID)
        return repeat_atom

    def _cin_stmt(self, additional_syncset):
        cin_atom = Atom(self._curr, 'cin: Ø')
        self._get_token()
        id_atom = self._curr
        if self._sync(self._ID, frozenset({';'}) | self._follow_dl | additional_syncset, self._ID):
            cin_atom.lexeme = f'cin: {id_atom.lexeme}'
            cin_atom._id_location = id_atom.location
        self._sync(';', self._follow_dl | additional_syncset, self._ID)
        return cin_atom

    def _cout_stmt(self, additional_syncset):
        cout_atom = Atom(self._curr)
        self._get_token()
        self._expression(additional_syncset).parent = cout_atom
        self._sync(';', self._follow_dl | additional_syncset, self._ID)
        return cout_atom

    def _block(self, additional_syncset):
        self._sync('{', self._follow_dl | additional_syncset, self._ID)
        sl = self._statement_list(additional_syncset)
        self._sync('}', self._follow_dl | additional_syncset, self._ID)
        return sl

    def _break_stmt(self, additional_syncset):
        break_atom = Atom(self._curr)
        self._get_token()
        self._sync(';', self._follow_dl | additional_syncset, self._ID)
        return break_atom

    def _assignment(self, additional_syncset):
        var = Atom(self._curr, f'{self.assignment_label} {self._curr.lexeme}')
        self._get_token()
        if self._curr.lexeme == ':=':
            self._get_token()
            self._expression(additional_syncset).parent = var
        elif self._curr.lexeme in self._first_una:
            operator = Atom(self._curr, self._curr.lexeme[0], parent=var)
            self._get_token()
            Atom(Token(var.lexeme.split()[-1], var.category, operator.location), parent=operator, _inc_dec=True)
            Atom(Token('1', self.tokenizer.int_label, operator.location), parent=operator)
        else:
            self._sync(tuple(self._first_at), self._first_exp | frozenset({';'}) | self._follow_dl | additional_syncset, self._ID_NUM)
            if self._independent(self._first_exp):
                self._expression(additional_syncset).parent = var
        self._sync(';', self._follow_dl | additional_syncset, self._ID)
        return var

    def _pre(self, additional_syncset):
        operator = Atom(self._curr, self._curr.lexeme[0])
        self._get_token()
        var = Atom(self._curr, f'{self.assignment_label} Ø')
        temp = self._curr.lexeme
        if self._sync(self._ID, frozenset({';'}) | self._follow_dl | additional_syncset, self._ID):
            var.lexeme = f'{self.assignment_label} {temp}'
        operator.parent = var
        Atom(Token(var.lexeme.split()[-1], var.category, operator.location), parent=operator, _inc_dec=True)
        Atom(Token('1', self.tokenizer.int_label, operator.location), parent=operator)
        self._sync(';', self._follow_dl | additional_syncset, self._ID)
        return var

    def _independent_id(self):
        return self._check_id_num(self._ID) and self._lookahead(self._curr).lexeme not in self._first_at

    def _independent(self, first_set):
        return self._curr.lexeme in first_set or self._check_id_num(self._NUM) or self._independent_id()

    def _extend_exp(self, op, old_exp, new_exp, additional_syncset, condition):
        self._sync(op.lexeme, self._first_exp | self._follow_dl | additional_syncset, self._ID_NUM)
        old_exp.parent = op
        new_exp(additional_syncset, condition).parent = op
        return op

    def _expression(self, additional_syncset, condition=False):
        temp = self._simple_expression(additional_syncset, condition)
        if self._curr.lexeme in self._first_rel:
            temp = self._extend_exp(Atom(self._curr), temp, self._simple_expression, additional_syncset, condition)
        return temp

    def _simple_expression(self, additional_syncset, condition):
        temp = self._term(additional_syncset, condition)
        while self._curr.lexeme in self._first_add:
            temp = self._extend_exp(Atom(self._curr), temp, self._term, additional_syncset, condition)
        return temp

    def _term(self, additional_syncset, condition):
        temp = self._superfactor(additional_syncset, condition)
        while self._curr.lexeme in self._first_mul or condition and self._independent(self._first_fact):
            if self._curr.lexeme in self._first_mul:
                temp = self._extend_exp(Atom(self._curr), temp, self._superfactor, additional_syncset, condition)
            else:
                temp = self._extend_exp(Atom(self._curr, self.expected_op_label), temp, self._superfactor, additional_syncset, condition)
                temp.lexeme = 'Ø'
        return temp

    def _superfactor(self, additional_syncset, condition):
        if self._curr.lexeme in self._first_add:
            sign = Atom(self._curr)
            self._get_token()
            self._factor(additional_syncset, condition).parent = sign
            return sign
        else:
            return self._factor(additional_syncset, condition)

    def _factor(self, additional_syncset, condition):
        if self._curr.lexeme == '(':
            self._get_token()
            temp = self._expression(additional_syncset, condition)
            self._sync(')', self._follow_fact | self._follow_dl | additional_syncset, self._ID)
        elif self._check_id_num(self._ID_NUM) or self._curr.lexeme in ('True', 'False'):
            temp = Atom(self._curr)
            self._get_token()
        else:
            temp = Atom(self._curr, 'Ø')
            self._sync(tuple(self._first_fact) + self._ID_NUM, self._follow_fact | self._follow_dl | additional_syncset, self._ID)
        return temp

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'root={self.root!r}',
                f'errors={self.errors!r}',
                f'tokenizer={self.tokenizer!r}',
                f'_tokens={self._tokens!r}',
                f'_curr={self._curr!r}',
                f'_ID={self._ID!r}',
                f'_NUM={self._NUM!r}',
                f'_ID_NUM={self._ID_NUM!r}',
                f'list_category={self.list_category!r}',
                f'dl_label={self.dl_label!r}',
                f'sl_label={self.sl_label!r}',
                f'decl_starter_label={self.decl_starter_label!r}',
                f'stmt_starter_label={self.stmt_starter_label!r}',
                f'indep_id_label={self.indep_id_label!r}',
                f'expected_op_label={self.expected_op_label!r}',
                f'lexical_error_at={self.lexical_error_at!r}',
                f'error_at_label={self.error_at_label!r}',
                f'expected_label={self.expected_label!r}',
                f'assignment_label={self.assignment_label!r}',
                f'error_before={self.error_before!r}',
                f'error_after={self.error_after!r}',
                f'output_dir={self.output_dir!r}']
        return f'{classname}({", ".join(args)})'


if __name__ == '__main__':
    Taurus(Flix(sys.argv[1])).write_output(render_file='tree.pdf')
