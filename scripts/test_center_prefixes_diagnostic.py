#!/usr/bin/env python3
"""Static tests only: never invoke Lean or the diagnostic runner."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import diagnose_center_prefixes as d

PACKET = d.ci.ROOT/'quartics/quartic-318-326/proof/experiments'/d.PACKET
SOURCE = (PACKET/(d.SOURCE+'.lean')).read_text()

class PrefixTests(unittest.TestCase):
    def test_exact_prefixes(self):
        cases = d.variants(SOURCE)
        self.assertEqual(len(cases),4)
        for name,text in cases.items():
            suffix = '\nend IntegralOverlapRootGenerators318\n'
            prefix = text[:-len(suffix)]
            self.assertTrue(SOURCE.startswith(prefix))
            self.assertNotIn('sorry',text)
            self.assertIn('set_option maxHeartbeats 1200000',text)
            self.assertNotIn('theorem finiteBaseChange_generator',text)
        self.assertNotIn('local instance infinityAlgebra',cases['concrete_context'])
        self.assertIn('local instance infinityAlgebra',cases['infinity_algebra'])
        self.assertNotIn('def finiteGenerator',cases['infinity_algebra'])
        self.assertIn('def finiteGenerator',cases['finite_generator'])
        self.assertNotIn('def infinityGenerator',cases['finite_generator'])
        self.assertIn('def infinityGenerator',cases['all_generators'])
    def test_mutation_rejected(self):
        with self.assertRaises(ValueError): d.variants(SOURCE+'\n')
    def test_hosted_guard(self):
        with patch.dict(d.os.environ,{},clear=True):
            with self.assertRaisesRegex(ValueError,'Hosted'): d.validate(PACKET,Path('/nonexistent'))
    def test_full_result_required(self):
        with tempfile.TemporaryDirectory() as t:
            with self.assertRaisesRegex(ValueError,'Mandatory full'): d.validate(PACKET,Path(t),hosted=False)
    def test_wrong_result_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);(out/'RESULT.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'Wrong full'): d.validate(PACKET,out,hosted=False)
    def test_compiled_dependency_required(self):
        with tempfile.TemporaryDirectory() as t:
            out=Path(t);r={'packet':d.PACKET,'packet_sha256':d.INTAKE_SHA,'commands':[{'module':d.DEPENDENCY,'exit_code':0}]}
            (out/'RESULT.json').write_text(json.dumps(r))
            with self.assertRaisesRegex(ValueError,'compiled dependency'): d.validate(PACKET,out,hosted=False)
            (out/'lib').mkdir();(out/'lib'/(d.DEPENDENCY+'.olean')).write_text('test fixture only, never loaded by Lean')
            cases,_=d.validate(PACKET,out,hosted=False);self.assertEqual(len(cases),4)
    def test_no_acceptance_or_olean(self):
        self.assertEqual(d.SECONDS,90)
        self.assertEqual(d.runner.original.SECONDS,90)
        text=Path(d.__file__).read_text()
        self.assertIn("'writes_olean': False",text)
        self.assertIn("'full_packet_accepted': False",text)
        self.assertNotIn("'-o'",text)
if __name__=='__main__': unittest.main()
