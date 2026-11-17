"""Isolated temporary-Git regression tests; no network or project writes."""
import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from check_integration_recovery import EXPERIMENTS, validate


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Recovery test fixture')
        self.git('config', 'user.email', 'test@example.invalid')
        marker = self.repo / '.github/inventory-requests/progress.json'
        marker.parent.mkdir(parents=True)
        marker.write_text('{}\n')
        names = ['fixture-r' + str(i) for i in range(16)]
        for name in names:
            p = self.repo / EXPERIMENTS / name / 'intake.json'
            p.parent.mkdir(parents=True)
            p.write_text('{}\n')
        registry = self.repo / EXPERIMENTS / 'packets.json'
        registry.write_text(json.dumps({'active_packets': names}) + '\n')
        note = self.repo / 'fixture-note.txt'
        note.write_text('before\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture parent')
        parent = self.git('rev-parse', 'HEAD')
        note.write_text('after\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture serial')
        anchor = self.git('rev-parse', 'HEAD')
        tree = self.git('rev-parse', 'HEAD^{tree}')
        serial = {'status': 'PASS_EXACT_SERIAL_NOT_LEAN', 'commit': anchor, 'tree': tree, 'parent': parent,
                  'files': [{'path': 'fixture-note.txt', 'sha256': self.sha(b'after\n'), 'previous_sha256': self.sha(b'before\n')}]}
        review = self.record('fixture-serial', 'serial', serial)
        publication = self.record('fixture-publication', 'publication', {'status': 'PUBLISHED_REMOTE_VERIFIED', 'commit': anchor,
            'tree': tree, 'parent': parent, 'remote': anchor, 'review_sha256': review['sha256']})
        self.checkpoint = {'schema': 'integration-recovery-v1', 'runtime_acceptance': False,
            'source_anchor': {'commit': anchor, 'tree': tree}, 'registry_sha256': self.sha(registry.read_bytes()),
            'active_packets': [{'name': n, 'tree': self.git('rev-parse', anchor + ':' + EXPERIMENTS + n)} for n in names],
            'receipts': [review, publication]}

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], stderr=subprocess.PIPE).decode().strip()

    @staticmethod
    def sha(raw):
        return hashlib.sha256(raw).hexdigest()

    @classmethod
    def record(cls, name, kind, data):
        raw = json.dumps(data, indent=2) + '\n'
        return {'name': name, 'kind': kind, 'raw_utf8': raw, 'sha256': cls.sha(raw.encode())}

    def rejected(self, mutate):
        c = copy.deepcopy(self.checkpoint)
        mutate(c)
        with self.assertRaises(ValueError):
            validate(self.repo, c)

    def rewrite_serial(self, c, mutate):
        data = json.loads(c['receipts'][0]['raw_utf8']); mutate(data)
        c['receipts'][0] = self.record('fixture-serial', 'serial', data)
        pub = json.loads(c['receipts'][1]['raw_utf8']); pub['review_sha256'] = c['receipts'][0]['sha256']
        c['receipts'][1] = self.record('fixture-publication', 'publication', pub)

    def test_valid(self):
        result = validate(self.repo, self.checkpoint)
        self.assertFalse(result['runtime_acceptance'])
        self.assertEqual(result['active_packets'], 16)

    def test_reject_runtime_claim(self):
        self.rejected(lambda c: c.update(runtime_acceptance=True))

    def test_reject_registry_hash(self):
        self.rejected(lambda c: c.update(registry_sha256='0' * 64))

    def test_reject_packet_order(self):
        self.rejected(lambda c: c['active_packets'].reverse())

    def test_reject_packet_tree(self):
        self.rejected(lambda c: c['active_packets'][0].update(tree=c['source_anchor']['tree']))

    def test_reject_raw_receipt_mutation(self):
        self.rejected(lambda c: c['receipts'][0].update(raw_utf8=c['receipts'][0]['raw_utf8'] + ' '))

    def test_reject_duplicate_receipts(self):
        self.rejected(lambda c: c['receipts'].append(copy.deepcopy(c['receipts'][0])))

    def test_reject_missing_serial_gate(self):
        self.rejected(lambda c: c['receipts'].pop(0))

    def test_reject_wrong_parent_even_rehashed(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r.update(parent=r['commit'])))

    def test_reject_nonpass_even_rehashed(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r.update(status='PENDING')))

    def test_reject_wrong_file_even_rehashed(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r['files'][0].update(sha256='0' * 64)))

    def test_reject_wrong_preimage_even_rehashed(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r['files'][0].update(previous_sha256='0' * 64)))

    def test_reject_null_preimage_for_existing_file(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r['files'][0].update(previous_sha256=None)))

    def test_accept_proven_new_file(self):
        parent = self.checkpoint['source_anchor']['commit']
        (self.repo / 'new-fixture.txt').write_text('new\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'new file fixture')
        anchor = self.git('rev-parse', 'HEAD')
        tree = self.git('rev-parse', 'HEAD^{tree}')
        c = copy.deepcopy(self.checkpoint)
        c['source_anchor'] = {'commit': anchor, 'tree': tree}
        serial = {'status': 'PASS_EXACT_SERIAL_NOT_LEAN', 'commit': anchor, 'tree': tree, 'parent': parent,
                  'files': [{'path': 'new-fixture.txt', 'sha256': self.sha(b'new\n'), 'previous_sha256': None}]}
        review = self.record('new-serial', 'serial', serial)
        publication = self.record('new-publication', 'publication', {'status': 'PUBLISHED_REMOTE_VERIFIED',
            'commit': anchor, 'tree': tree, 'parent': parent, 'remote': anchor, 'review_sha256': review['sha256']})
        c['receipts'] = [review, publication]
        self.assertFalse(validate(self.repo, c)['runtime_acceptance'])

    def test_reject_path_traversal(self):
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r['files'][0].update(path='../outside')))

    def test_reject_nonancestor(self):
        raw = subprocess.check_output(['git', '-C', str(self.repo), 'commit-tree', self.checkpoint['source_anchor']['tree']], input=b'fixture orphan\n')
        orphan = raw.decode().strip()
        self.rejected(lambda c: self.rewrite_serial(c, lambda r: r.update(commit=orphan)))


if __name__ == '__main__':
    unittest.main()
