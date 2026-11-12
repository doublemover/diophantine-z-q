#!/usr/bin/env python3
"""Collector-only regression fixtures. Does not invoke Lean or access a user audit."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import zipfile
from collect_windows_audit_failures import collect

class CollectorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)
        self.run = self.base / 'windows-fixture'
        self.run.mkdir()
    def tearDown(self):
        self.temp.cleanup()
    def write(self, path, value):
        p = self.run / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(value if isinstance(value, str) else json.dumps(value), encoding='utf-8')
        return p
    def collect(self, **kw):
        return collect(self.run, self.base / 'report', **kw)
    def test_all_three_lean_failures_and_infrastructure(self):
        names = ['ContactOriginalRestrictionCoordinates318', 'ActualCanonicalOverlap318', 'ThreePoleCertificates318']
        self.write('summary.json', {'status':'FAILED', 'head':'abc', 'active_packets':['one','two','three','blocked'],
            'stages': {'packet-one': {'exit_code':1}, 'cohort-b': {'exit_code':2}}, 'packets': {'one':1,'two':1,'three':1}})
        for packet, name in zip(['one','two','three'], names):
            self.write('packet-output-' + packet + '/RESULT.json', {'status':'FAILED','commands':[{'module':name,'exit_code':1}]})
            self.write('packet-output-' + packet + '/logs/' + name + '.log', name + '.lean:9:2: error: unknown identifier\n')
        self.write('cohort-b.log', 'PermissionError: Access denied\n')
        self.write('exception.log', 'Traceback (most recent call last):\nRuntimeError: packets failed\n')
        self.write('orphan.log', 'WALL_CLOCK_LIMIT_EXCEEDED\n')
        self.write('build/lib/huge.olean', 'artifact')
        result, archive = self.collect()
        rows = {r['source']: r for r in result['records']}
        for packet, name in zip(['one','two','three'], names):
            self.assertIn('packet-output-' + packet + '/logs/' + name + '.log', rows)
        self.assertIn('orphan.log', rows)
        self.assertTrue(rows['packet-one.log']['missing_log'])
        self.assertEqual(rows['summary.json']['packets_without_completion'], ['blocked'])
        with zipfile.ZipFile(archive) as z:
            self.assertEqual(set(z.namelist()), {'failures.json','failures.txt'})
    def test_nonzero_exit_without_diagnostic_marker_and_duplicate_module(self):
        self.write('summary.json', {'status':'FAILED','stages':{'packet-a':{'exit_code':7}}})
        self.write('packet-a.log', json.dumps({'module':'M','exit_code':7})+'\n')
        self.write('packet-output-a/logs/M.log', 'silently terminated\n')
        self.write('packet-output-b/logs/M.log', 'unrelated successful module\n')
        result, _ = self.collect()
        rows = {r['source']:r for r in result['records']}
        self.assertIn('packet-output-a/logs/M.log',rows)
        self.assertNotIn('packet-output-b/logs/M.log',rows)
        self.assertTrue(rows['packet-output-a/logs/M.log']['excerpt'])
    def test_no_record_count_cap_and_bounded_excerpts(self):
        for i in range(120):
            self.write(f'logs/{i}.log', ('x: error: mismatch\n' * 2000))
        result, archive = self.collect(excerpt_chars=1024)
        self.assertEqual(len(result['records']),120)
        for row in result['records']:
            self.assertEqual(row['diagnostic_fragments'],2000)
            self.assertTrue(row['matching_line_index_truncated'])
            self.assertLessEqual(sum(len(x['text'])+32 for x in row['excerpt']),1024)
        self.assertLess(archive.stat().st_size,100000)
    def test_long_line_utf16_and_invalid_utf8(self):
        p=self.write('long.log','error: '+'a'*200000+'\nend\n')
        expected=hashlib.sha256(p.read_bytes()).hexdigest()
        (self.run/'utf16.log').write_text('fatal: unicode failure\n',encoding='utf-16')
        (self.run/'bad.log').write_bytes(b'error: \xff\n')
        result,_=self.collect()
        rows={r['source']:r for r in result['records']}
        self.assertEqual(rows['long.log']['sha256'],expected)
        self.assertGreater(rows['long.log']['long_or_final_line_fragments'],0)
        self.assertEqual(rows['utf16.log']['encoding'],'utf-16')
        self.assertEqual(rows['bad.log']['decoding_replacement_fragments'],1)
    def test_malformed_metadata_running_and_empty_log(self):
        self.write('summary.json',{'status':'RUNNING','stages':{'cohort-x':{'exit_code':1}}})
        self.write('RESULT.json','{truncated')
        self.write('cohort-x.log','')
        result,_=self.collect()
        self.assertFalse(result['collector_complete'])
        rows={r['source']:r for r in result['records']}
        self.assertIn('summary.json',rows)
        self.assertEqual(rows['cohort-x.log']['excerpt'],[])
        self.assertTrue(result['collection_problems'])
    def test_no_overwrite_or_inside_input(self):
        with self.assertRaises(ValueError):
            collect(self.run,self.run/'report')
        self.write('ok.log','ok')
        self.collect()
        with self.assertRaises(FileExistsError):
            self.collect()
    def test_no_logs_is_incomplete(self):
        result,_=self.collect()
        self.assertFalse(result['collector_complete'])
    def test_symlink_is_not_followed(self):
        outside=self.base/'external.log';outside.write_text('error: outside')
        try:
            (self.run/'linked.log').symlink_to(outside)
        except (OSError,NotImplementedError):
            self.skipTest('No symlink privilege on this platform')
        result,_=self.collect()
        self.assertEqual(result['logs_scanned'],0)
        self.assertFalse(result['collector_complete'])

if __name__=='__main__':
    unittest.main()
