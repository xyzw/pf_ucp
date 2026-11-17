"""Regression checks for vendored dependency discovery and invalidation."""

from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from local_modules import dependency_order, local_imports
from snapshot_reuse import reusable_dependency_closure


class LocalModulesTests(unittest.TestCase):
    def test_comments_and_multiple_imports(self):
        source = '''/- import GptLean.Fake /- nested -/ -/
module
import GptLean.Real import PfHk.Other -- import PfHk.Fake
import Mathlib.Analysis
public import GptLean.Nested.Real
'''
        self.assertEqual(local_imports(source),
                         {'GptLean.Real', 'PfHk.Other', 'GptLean.Nested.Real'})

    def test_multiline_import_header_and_body_strings(self):
        source = '''module
prelude
public meta import
  GptLean.Base
import /- comment
  /- nested -/ -/ GptLean.Middle
import all PfHk.Main
def text := "import GptLean.Fake"
'''
        self.assertEqual(local_imports(source),
                         {'GptLean.Base', 'GptLean.Middle', 'PfHk.Main'})
        with self.assertRaisesRegex(ValueError, 'Unsupported'):
            local_imports('import GptLean.\u00abquoted name\u00bb')

    def test_nested_vendor_closure_excludes_unselected_drafts(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            files = {'PfHk.lean': 'import PfHk.Main',
                     'PfHk/Main.lean': 'import GptLean.Nested.Base',
                     'GptLean/Nested/Base.lean': 'import Mathlib',
                     'PfHk/Draft.lean': 'import GptLean.Missing'}
            for name, content in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            self.assertEqual([str(p.relative_to(root)) for p in dependency_order(root, ['PfHk'])],
                             ['GptLean/Nested/Base.lean', 'PfHk/Main.lean', 'PfHk.lean'])
            with self.assertRaisesRegex(ValueError, 'Missing local module'):
                dependency_order(root, ['PfHk.Draft'])
            (root / 'GptLean/Nested/Base.lean').write_text('import PfHk.Main')
            with self.assertRaisesRegex(ValueError, 'cycle'):
                dependency_order(root, ['PfHk'])

    def test_vendor_change_invalidates_downstream_proofs(self):
        dependencies = {'GptLean.Base': set(), 'GptLean.Middle': {'GptLean.Base'},
                        'PfHk.Main': {'GptLean.Middle'}, 'PfHk.Other': set()}
        self.assertEqual(reusable_dependency_closure(
            set(dependencies) - {'GptLean.Base'}, dependencies), {'PfHk.Other'})


if __name__ == '__main__':
    unittest.main()
