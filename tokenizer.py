r"""Lexical analyzer for the "Tiny-Extended" programming language.

The recognized tokens are:
    Keywords:          main, int, real, boolean, if, then, else, while, repeat, until, cin, cout
    Symbols:           { } ; , ( ) := ++ -- < <= > >= == != + - * /
    Id:                [A-Za-z][A-Za-z0-9_]*
    Number:            [0-9]+(\.[0-9]+)?
    Block comment:     /\*.*?\*/
    Inline comment:    //[^\n]*

This module exports:
  - Token    class containing the lexeme, category and location of the found token.
  - Flix     class that converts an input file into a sequence of tokens.
"""

from pathlib import Path
import sys
import re


class Token:
    """Class containing the lexeme, category and location of a token."""
    __slots__ = ('lexeme', 'category', 'location')

    def __init__(self, lexeme, category, location):
        """A simple token instance.

        :param lexeme: The token's lexeme.
        :param category: The token's category.
        :param location: The token's location on the scanned source file.
        """
        self.lexeme = lexeme
        self.category = category
        self.location = location

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'{self.lexeme!r}', f'{self.category!r}', f'{self.location!r}']
        return f'{classname}({", ".join(args)})'


class Flix:
    """Convert an input file into a sequence of tokens.

        Output can be customized by subclassing and redefining the following:
            Token category labels (cannot contain whitespace):
              - id_label
              - keyword_label
              - int_label
              - real_label
              - boolean_label
              - op_label
              - special_label
            Formatting separators:
              - tokens_separator
              - errors_separator
            Tab character length:
              - tab_length
            Invalid file error message:
              - invalid_file_msg
            Output directory:
              - output_dir

        Public methods:
          - scan            Read the input file one line at a time and yield the tokens and errors found.
          - write_output    Write tokens and errors to their respective specified files.
    """
    id_label = 'ID'
    keyword_label = 'KEYWORD'
    int_label = 'INT'
    real_label = 'REAL'
    boolean_label = 'BOOLEAN'
    op_label = 'OP'
    special_label = 'SPECIAL'
    tokens_separator = '.' * 5
    errors_separator = ' unexpected at '
    tab_length = 4
    invalid_file_msg = 'The input file does not exist or is empty.'
    output_dir = Path('Lexicon')

    _keywords = frozenset(
        {'main', 'int', 'real', 'boolean', 'if', 'then', 'else', 'while', 'repeat', 'until', 'cin', 'cout', 'coutln', 'rompe'})
    _block_end = re.compile(r'[^\n]*\*/')

    def __init__(self, input_file):
        """A Flix object used for scanning a file.

        :param input_file: Source code to be scanned.
        """
        self._input_file = Path(input_file)
        self._token_groups = [
            ('skip', r'\s+|//[^\n]*|/\*.*?\*/'),
            ('block_start', r'/\*[^\n]*'),
            (self.real_label, r'[0-9]+\.[0-9]+'),
            (self.boolean_label, r'True|False'),
            (self.int_label, r'[0-9]+'),
            (self.id_label, r'[A-Za-z][A-Za-z0-9_]*'),
            (self.special_label, r'[{};,()]'),
            (self.op_label, r'\+{1,2}|-{1,2}|(?:<|>)=?|(?::|=|!)=|[*/]'),
            ('error', r'.'),
        ]
        self._token_pattern = re.compile('|'.join(f'(?P<{tg[0]}>{tg[1]})' for tg in self._token_groups))

    @staticmethod
    def _replace_tabs(string, tab_length):
        column = 0
        newstring = ''
        for c in string:
            if c == '\t':
                if column % tab_length == 0:
                    n = tab_length
                else:
                    n = 0
                    while column % tab_length != 0:
                        n += 1
                        column += 1
                spaces = ' ' * n
                newstring = f'{newstring}{spaces}'
            elif c == '\n':
                column = 0
                newstring = f'{newstring}{c}'
            else:
                column += 1
                newstring = f'{newstring}{c}'
        return newstring

    def scan(self):
        """Read the input file one line at a time and yield the tokens and errors found."""
        if self.input_file.is_file() and self.input_file.stat().st_size > 0:
            line_num = 0
            block_comment_mode = False
            with self.input_file.open(encoding='utf-8') as source_code:
                for line in source_code:
                    if '\t' in line:
                        line = self._replace_tabs(line, self.tab_length)
                    line_num += 1
                    start_pos = 0
                    if block_comment_mode and self._block_end.match(line):
                        block_comment_mode = False
                        start_pos = self._block_end.match(line).end()
                    if not block_comment_mode:
                        for m in self._token_pattern.finditer(line, start_pos):
                            category = m.lastgroup
                            lexeme = m.group(category)
                            if category == 'skip':
                                pass
                            elif category == 'block_start':
                                block_comment_mode = True
                            else:
                                if category == self.id_label and lexeme in self._keywords:
                                    category = self.keyword_label
                                column = m.start() + 1  # Column number starts at 1
                                yield Token(lexeme, category, f'{line_num}:{column}')
        else:
            raise RuntimeError(self.invalid_file_msg)

    def write_output(self, tokens_filename='tokens.txt', errors_filename='errors.txt'):
        """Write tokens and errors to their respective specified files.

        :param tokens_filename: Name of the file to write the tokens into. Default: tokens.txt.
        :param errors_filename: Name of the file to write the errors into. Default: errors.txt.
        """
        self.output_dir.mkdir(parents=True, exist_ok=True)
        with (self.output_dir / tokens_filename).open('w', encoding='utf-8') as tokens_file, \
                (self.output_dir / errors_filename).open('w', encoding='utf-8') as errors_file:
            for tkn in self.scan():
                if tkn.category == 'error':
                    errors_file.write(f'\'{tkn.lexeme}\'{self.errors_separator}{tkn.location}\n')
                else:
                    tokens_file.write(f'{tkn.lexeme}{self.tokens_separator}{tkn.category}{self.tokens_separator}{tkn.location}\n')

    @property
    def input_file(self):
        """Source code to be scanned."""
        return self._input_file

    @input_file.setter
    def input_file(self, value):
        self._input_file = Path(value)

    def __repr__(self):
        classname = self.__class__.__name__
        args = [f'input_file={self.input_file!r}',
                f'id_label={self.id_label!r}',
                f'keyword_label={self.keyword_label!r}',
                f'int_label={self.int_label!r}',
                f'real_label={self.real_label!r}',
                f'boolean_label={self.boolean_label!r}',
                f'op_label={self.op_label!r}',
                f'special_label={self.special_label!r}',
                f'tokens_separator={self.tokens_separator!r}',
                f'errors_separator={self.errors_separator!r}',
                f'tab_length={self.tab_length!r}',
                f'invalid_file_msg={self.invalid_file_msg!r}',
                f'output_dir={self.output_dir!r}',
                f'_keywords={self._keywords!r}',
                f'_token_groups={self._token_groups!r}',
                f'_block_end={self._block_end!r}',
                f'_token_pattern={self._token_pattern!r}']
        return f'{classname}({", ".join(args)})'


if __name__ == '__main__':
    Flix(sys.argv[1]).write_output()
