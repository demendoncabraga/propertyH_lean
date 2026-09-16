"""Regression tests for the Osajda-only terminal scope gate."""
import copy
import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
from types import SimpleNamespace
from check_dependencies import check
from audit import EXTERNAL_ASSUMPTIONS, validate_terminal_scope


class TerminalScopeTests(unittest.TestCase):
    def setUp(self):
        self.coverage = dict(inventory_complete=True,
                             verification_scope='modulo_osajda')
        self.items = [dict(id='proved', status='verified', declaration='PropertyH.result')]
        self.items += [dict(id=name, status='external_assumption', declaration=name)
                       for name in sorted(EXTERNAL_ASSUMPTIONS)]

    def test_exact_osajda_hypothesis_accepted(self):
        validate_terminal_scope(self.coverage, self.items, True)

    def test_unconditional_gate_does_not_accept_assumptions(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, self.items, False)

    def test_additional_assumption_rejected(self):
        items = self.items + [dict(id='extra', status='external_assumption', declaration='Extra')]
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, items, True)

    def test_missing_or_replaced_assumption_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, self.items[:-1], True)
        items = copy.deepcopy(self.items)
        items[-1]['declaration'] = 'UnexpectedReplacement'
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, items, True)

    def test_proof_debt_or_incomplete_inventory_rejected(self):
        items = copy.deepcopy(self.items)
        items[0]['status'] = 'in_progress'
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, items, True)
        coverage = dict(self.coverage, inventory_complete=False)
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(coverage, self.items, True)

    def test_maurey_pisier_cannot_be_reintroduced(self):
        items = self.items + [dict(id='MP', status='external_assumption',
                                  declaration='PropertyH.MaureyPisierFiniteRepresentability')]
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, items, True)
        coverage = dict(self.coverage, verification_scope='modulo_maurey_pisier_and_osajda')
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(coverage, self.items, True)

    def test_duplicate_osajda_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, self.items + [self.items[-1]], True)

    def test_undeclared_scope_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(inventory_complete=True), self.items, True)


class DependencyScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'lean/PropertyH').mkdir(parents=True)
        (self.root / 'lean/PropertyH/Final.lean').write_text('-- fixture\n')
        self.index = self.root / '.lake/build/lib/lean/PropertyH/Final.ilean'
        self.index.parent.mkdir(parents=True)
        self.data = dict(decls={name: [i, 0, i, 10] for i, name in enumerate(
            ['PropertyH.result', 'PropertyH.helper', 'PropertyH.tacticHelper'])}, references={
                json.dumps(dict(c=dict(m='PropertyH.Final', n='PropertyH.tacticHelper'))):
                    dict(usages=[[0, 0, 0, 1, 'PropertyH.result']])})
        self.kernel = dict(roots=['PropertyH.result'], declarations=[
            dict(name='PropertyH.result', deps=['PropertyH.helper']),
            dict(name='PropertyH.helper', deps=[])])
        self.inventory = dict(paper_roots=self.kernel['roots'],
                              items=[dict(declaration=n) for n in self.data['decls']])

    def run_check(self):
        self.index.write_text(json.dumps(self.data))
        (self.root / 'lean/coverage.json').write_text(json.dumps(self.inventory))
        with patch('check_dependencies.subprocess.run', return_value=SimpleNamespace(
                stdout=json.dumps(self.kernel))), patch('builtins.print'):
            check(self.root)

    def test_kernel_and_tactic_dependencies_retained(self):
        self.run_check()

    def test_unused_declaration_rejected(self):
        self.data['decls']['PropertyH.obsolete'] = [9, 0, 9, 10]
        self.inventory['items'].append(dict(declaration='PropertyH.obsolete'))
        with self.assertRaisesRegex(RuntimeError, 'outside the final proof'):
            self.run_check()

    def test_missing_inventory_entry_rejected(self):
        self.inventory['items'].pop()
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_stale_inventory_entry_rejected(self):
        self.inventory['items'].append(dict(declaration='PropertyH.removed'))
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_missing_kernel_source_rejected(self):
        self.kernel['declarations'].append(dict(name='PropertyH.missing', deps=[]))
        with self.assertRaisesRegex(RuntimeError, 'no source declaration'):
            self.run_check()

    def test_wrong_roots_rejected(self):
        self.inventory['paper_roots'] = ['PropertyH.wrong']
        with self.assertRaisesRegex(RuntimeError, 'Paper roots differ'):
            self.run_check()


if __name__ == '__main__':
    unittest.main()
