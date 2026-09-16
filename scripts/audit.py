#!/usr/bin/env python3
"""Build PropertyH and audit the declarations registered in its coverage inventory."""

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


def lean_code(text):
    """Remove nested block comments, line comments and strings for a keyword scan."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def fail(message):
    raise RuntimeError(message)



EXTERNAL_ASSUMPTIONS = {
    'PropertyH.MaureyPisierFiniteRepresentability',
    'PropertyH.OsajdaExpanderGroup',
}


def validate_terminal_scope(coverage, items, modulo_external=False):
    """Require closed proof coverage, allowing only the two explicitly named hypotheses."""
    permitted = {'verified', 'external_assumption'} if modulo_external else {'verified'}
    unfinished = [item['id'] for item in items if item['status'] not in permitted]
    if coverage.get('inventory_complete') is not True or unfinished or not items:
        fail('Formalization is incomplete. Complete the inventory and verify every entry. '
             'Open entries: ' + ', '.join(unfinished))
    if modulo_external:
        externals = [i.get('declaration') for i in items if i['status'] == 'external_assumption']
        if len(externals) != 2 or set(externals) != EXTERNAL_ASSUMPTIONS:
            fail('Modulo scope must name exactly Maurey–Pisier and Osajda, each once.')
        if coverage.get('verification_scope') != 'modulo_maurey_pisier_and_osajda':
            fail('Coverage does not declare the authorized modulo scope.')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terminal', action='store_true', help='require complete coverage and proofs')
    parser.add_argument('--modulo-external', action='store_true',
                        help='with --terminal, allow exactly the explicit MP and Osajda hypotheses')
    args = parser.parse_args()
    if args.modulo_external and not args.terminal:
        fail('--modulo-external requires --terminal.')
    root = Path(__file__).resolve().parent.parent
    coverage = json.loads((root / 'lean/coverage.json').read_text())
    items = coverage.get('items', [])
    if not items or not isinstance(items, list):
        fail('The coverage inventory is empty or malformed.')
    ids = [item['id'] for item in items]
    if len(set(ids)) != len(ids):
        fail('Coverage IDs must be unique.')
    names = []
    for item in items:
        if item['status'] not in {'not_started', 'in_progress', 'verified', 'external_assumption'}:
            fail('Invalid status for ' + item['id'])
        name = item.get('declaration')
        if name:
            # Prevent newline or Lean-command injection in generated audit commands.
            if not isinstance(name, str) or re.search(r'[\s;`"\\]', name):
                fail('Expected a plain qualified declaration name for ' + item['id'])
            names.append(name)
        elif item['status'] in {'verified', 'external_assumption'}:
            fail('Verified entry has no declaration: ' + item['id'])
    names = list(dict.fromkeys(names))
    if args.terminal:
        validate_terminal_scope(coverage, items, args.modulo_external)
        if not names:
            fail('No declarations registered for terminal audit.')

    holes = []
    for path in sorted((root / 'lean').rglob('*.lean')):
        code = lean_code(path.read_text())
        for number, line in enumerate(code.splitlines(), 1):
            if re.search(r'\baxiom\b', line):
                fail(f'Project axiom declaration: {path.relative_to(root)}:{number}')
            if re.search(r'\b(sorry|admit|sorryAx)\b', line):
                holes.append(f'{path.relative_to(root)}:{number}')
    if holes:
        print('Unfinished proof terms: ' + ', '.join(holes), flush=True)
        if args.terminal:
            fail('Proof placeholders remain.')

    if shutil.which('lake') is None:
        fail('Lake is unavailable. Run sh scripts/setup.sh first.')
    subprocess.run(['lake', 'build'], cwd=root, check=True)
    audit = 'import PropertyH\n\n'
    audit += '-- Generated by scripts/audit.py from lean/coverage.json. Do not edit by hand.\n'
    if names:
        audit += '\n'.join('#print axioms ' + name for name in names) + '\n'
    else:
        audit += '-- No declarations have been registered yet; this is not a proof certificate.\n'
    (root / 'lean/Audit.lean').write_text(audit)
    result = subprocess.run(['lake', 'env', 'lean', 'lean/Audit.lean'], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        fail('Lean could not check the generated audit.')
    if not names:
        print('Build checked; no mathematical declarations are registered. Formalization not started.')
        return

    reports = {}
    for match in re.finditer(r"'([^\n]+)'\s+depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        reports[match[1]] = {s.strip() for s in match[2].split(',') if s.strip()}
    for match in re.finditer(r"'([^\n]+)'\s+does not depend on any axioms", result.stdout):
        reports[match[1]] = set()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in names:
        if name not in reports:
            fail('Missing or unrecognized axiom report for ' + name)
        item_statuses = [i['status'] for i in items if i.get('declaration') == name]
        permitted = allowed if args.terminal or 'verified' in item_statuses else allowed | {'sorryAx'}
        unexpected = reports[name] - permitted
        if unexpected:
            fail('Unexpected axioms for ' + name + ': ' + ', '.join(sorted(unexpected)))
    if args.terminal:
        if args.modulo_external:
            print('Terminal audit passed modulo explicit Maurey–Pisier and Osajda hypotheses. '
                  'No proof placeholders or nonstandard axioms. Source review is recorded separately.')
        else:
            print('Terminal mechanical audit passed. Source-to-statement review is also required.')
    else:
        print('Intermediate audit passed. This is not a completed-paper certificate.')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('Audit failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
