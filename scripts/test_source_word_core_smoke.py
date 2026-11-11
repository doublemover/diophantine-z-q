#!/usr/bin/env python3
import importlib.util
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
# Works installed in scripts or as an isolated proposal invoked with PYTHONPATH=scripts.
import check_source_word_core_smoke as s
class CoreSmokeTests(unittest.TestCase):
 def test_exact_transitive_closure(self):
  order=s.validate();self.assertEqual(len(order),117);self.assertEqual(order[-1],s.TARGETS[-1]);self.assertTrue(set(s.TARGETS).issubset(order))
 def test_upstream_is_subset_of_full_fetch(self):
  def imports(name):
   p=s.c.EXPERIMENTS/name;i=json.loads((p/"intake.json").read_text())
   return {d for n in i["order"] for d in i["files"][n+".lean"]["imports"] if d.startswith("Mathlib.")}
  self.assertLessEqual(imports(s.CORE),imports(s.PARENT))
 def test_binds_parent_and_primary_evidence(self):
  for name in [s.PARENT,s.CORE]:
   s.c.check_application_bindings(s.c.EXPERIMENTS/name)
  c=json.loads((s.c.EXPERIMENTS/s.CORE/'CLOSURE.json').read_text())
  self.assertEqual(c['parent_intake_sha256'],s.PARENT_INTAKE)
  self.assertEqual(c['parent_application_sha256'],s.PARENT_APPLICATION)
 def test_mutated_source_rejected(self):
  original=s.sha
  target=s.c.EXPERIMENTS/s.CORE/'CyclicQuotientEvaluation318.lean'
  with patch.object(s,'sha',side_effect=lambda p:'0'*64 if p==target else original(p)):
   # The normal application's own checker hashes through c.ci.sha; mutate that too.
   original_ci=s.c.ci.sha
   with patch.object(s.c.ci,'sha',side_effect=lambda p:'0'*64 if p==target else original_ci(p)):
    with self.assertRaises(ValueError):s.validate()
 def test_parent_revision_rejected(self):
  with patch.object(s,'PARENT_INTAKE','0'*64):
   with self.assertRaises(ValueError):s.validate()
 def test_standard_checker_and_same_budget(self):
  cmd=s.command(Path('/tmp/cache'),Path('/tmp/out'))
  self.assertIn('check_progress_experiment.py',cmd[2]);self.assertEqual(cmd[-2:],['--seconds','180'])
  self.assertEqual(cmd[3],'check');self.assertNotIn('-o',cmd)
  source=Path(s.__file__).read_text()
  self.assertNotIn('skipKernelTC',source);self.assertNotIn('continue-on-error',source)
 def test_scope_separate_and_no_registry_write(self):
  source=Path(s.__file__).read_text()
  self.assertIn("'full_packet_accepted':False",source)
  self.assertIn("'new_source_acceptance':False",source)
  self.assertIn("raise SystemExit(result.returncode)",source)
  self.assertNotIn("parent_result.write",source)
  self.assertNotIn("packets.json",source)
if __name__=='__main__':unittest.main()
