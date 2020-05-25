#!/usr/bin/env python3
#
# Creates a stdout file from running `rlox` on the given file
import os
import subprocess
import sys

def fail_if_fnf(f):
    if not os.access(f, os.F_OK):
        print(f'{sys.argv[0]}: error: {f}: file does not exist', file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(f'{sys.argv[0]}: usage: {sys.argv[0]} [test category] [test name]', file=sys.stderr)
        sys.exit(1)

    test = f'tests/lox/{sys.argv[1]}/{sys.argv[2]}.lox'
    fail_if_fnf(test)

    rlox = './target/debug/rlox'
    fail_if_fnf(rlox)

    try:
        out = subprocess.check_output([rlox, test])
    except CalledProcessError as e:
        print(f'{sys.argv[0]}: error: {e}')
        sys.exit(1)

    test_stdout = f'tests/output/{sys.argv[1]}/{sys.argv[2]}.stdout'
    fail_if_fnf('/'.join(test_stdout.split('/')[0:3]))
    with open(test_stdout, 'wb') as f:
        f.write(out)

