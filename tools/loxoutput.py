#!/usr/bin/env python3
'''Creates a stderr or stdout file for a lox test case.

    Typical usage example:
    % python3 loxoutput.py -type 'stdout' --category 'variable' --name 'global'
'''
from argparse import ArgumentParser
import os
import subprocess
import sys


def fail_if_fnf(path):
    '''Exits the program if 'path' is not accessible. '''
    if not os.access(path, os.F_OK):
        print(f'{sys.argv[0]}: error: {path}: file does not exist',
              file=sys.stderr)
        sys.exit(1)


def write_out(out='', category='', name='', ext=''):
    '''Writes 'out' to a stdout or stderr file. This truncates any existing file.'''
    test_out = f'tests/output/{category}/{name}.{ext}'
    fail_if_fnf('/'.join(test_out.split('/')[0:3]))
    with open(test_out, 'wb') as handle:
        handle.write(out)


if __name__ == '__main__':
    parser = ArgumentParser('Creates a stdout or stderr file from running '
                            '`rlox` on <category> and <name>\n')
    parser.add_argument('--type,-t', dest='type', required=True)
    parser.add_argument('--category,-c', dest='category', required=True)
    parser.add_argument('--name,-n', dest='name', required=True)
    args = parser.parse_args()

    test = f'tests/lox/{args.category}/{args.name}.lox'
    fail_if_fnf(test)

    RLOX = './target/debug/rlox'
    fail_if_fnf(RLOX)

    try:
        stdout = subprocess.check_output([RLOX, test], stderr=subprocess.PIPE)
        assert args.type == 'stdout'
    except subprocess.CalledProcessError as err:
        if args.type == 'stdout':
            print(f'{sys.argv[0]}: error: {err}')
            sys.exit(1)

        write_out(out=err.stderr,
                  category=args.category,
                  name=args.name,
                  ext='stderr')
    else:
        write_out(out=stdout,
                  category=args.category,
                  name=args.name,
                  ext='stdout')
