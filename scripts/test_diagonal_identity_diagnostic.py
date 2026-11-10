#!/usr/bin/env python3
"""Pure source tests; never executes Lean."""
import hashlib
from pathlib import Path
import unittest
import diagnose_diagonal_identity as d
class DiagonalTests(unittest.TestCase):
    def setUp(self):
        root=Path('quartics/quartic-318-326/proof/experiments')
        self.new=(root/d.PACKET/'OriginalGeometricDiagonal318.lean').read_text()
        self.old=(root/d.CONTROL_PACKET/'OriginalGeometricDiagonal318.lean').read_text()
    def test_binding(self):
        self.assertEqual(hashlib.sha256(self.new.encode()).hexdigest(),d.SOURCE_SHA)
        self.assertEqual(hashlib.sha256(self.old.encode()).hexdigest(),d.CONTROL_SHA)
    def test_original_proof_retained(self):
        body=self.old[self.old.index('lemma diagonal_to_split'):self.old.index('\nend OriginalGeometricDiagonal318')]
        self.assertIn(body,self.new)
        for key,text in d.variants(self.new,self.old).items():
            if key.endswith('full'):self.assertIn(body,text)
            else:self.assertNotIn('lemma diagonal_to_split',text)
    def test_memory_parser(self):
        self.assertEqual(d.parse_memory_status('Name: lean\nVmRSS: 120 kB\nVmHWM: 250 kB\n'),
            {'peak_rss_kib':120,'peak_hwm_kib':250})
        self.assertEqual(d.parse_memory_status('Name: lean\n'),{})
    def test_capture_and_nonadmission(self):
        self.assertEqual(len(d.variants(self.new,self.old)),4)
        for text in d.variants(self.new,self.old).values():
            self.assertNotIn('sorry',text)
            self.assertIn('set_option stderrAsMessages false',text)
            self.assertIn('set_option profiler.threshold 0 in',text)
            self.assertIn('private theorem diagnostic_positive_split_sections : True',text)
            if 'lemma diagonal_to_split' in text:
                self.assertIn('private theorem diagnostic_positive_diagonal_to_split : True',text)
            self.assertTrue(text.endswith('end OriginalGeometricDiagonal318\n'))
if __name__=='__main__': unittest.main()
