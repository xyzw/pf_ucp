"""Small checks for dependency propagation in optional verification reuse."""

import unittest

from snapshot_reuse import reusable_dependency_closure


class DependencyReuseTests(unittest.TestCase):
    def setUp(self):
        # Reverse order also checks independence from source-list ordering.
        self.dependencies = {
            'root': {'left', 'right'},
            'left': {'base'},
            'right': {'base'},
            'base': set(),
            'independent': set(),
        }

    def test_all_matching_modules_are_reused(self):
        self.assertEqual(
            reusable_dependency_closure(set(self.dependencies), self.dependencies),
            set(self.dependencies))

    def test_changed_dependency_invalidates_all_dependents(self):
        self.assertEqual(
            reusable_dependency_closure(set(self.dependencies) - {'base'}, self.dependencies),
            {'independent'})

    def test_changed_branch_keeps_other_branch(self):
        self.assertEqual(
            reusable_dependency_closure(set(self.dependencies) - {'left'}, self.dependencies),
            {'base', 'right', 'independent'})

    def test_missing_or_cyclic_dependencies_are_not_reused(self):
        dependencies = {'missing': {'absent'}, 'a': {'b'}, 'b': {'a'}, 'ok': set()}
        self.assertEqual(reusable_dependency_closure(set(dependencies), dependencies), {'ok'})


if __name__ == '__main__':
    unittest.main()
