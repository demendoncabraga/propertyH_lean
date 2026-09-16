"""Regression tests for the two-result terminal scope gate."""
import copy
import unittest
from audit import EXTERNAL_ASSUMPTIONS, validate_terminal_scope


class TerminalScopeTests(unittest.TestCase):
    def setUp(self):
        self.coverage = dict(inventory_complete=True,
                             verification_scope='modulo_maurey_pisier_and_osajda')
        self.items = [dict(id='proved', status='verified', declaration='PropertyH.result')]
        self.items += [dict(id=name, status='external_assumption', declaration=name)
                       for name in sorted(EXTERNAL_ASSUMPTIONS)]

    def test_exact_two_hypotheses_accepted(self):
        validate_terminal_scope(self.coverage, self.items, True)

    def test_unconditional_gate_does_not_accept_assumptions(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, self.items, False)

    def test_third_assumption_rejected(self):
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

    def test_undeclared_scope_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(inventory_complete=True), self.items, True)


if __name__ == '__main__':
    unittest.main()
