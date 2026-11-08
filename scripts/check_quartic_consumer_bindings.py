"""Verify the reviewed V10 -> V11 -> V13 document chain without editing old receipts.

This is a binding check, not a new mathematical acceptance. The component Lean
receipt remains immutable and its original prose is verified at the frozen snapshot.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
DECISIONS = {
    ('v11', 'group'): '5d85b1fb1beb79ff46fb1227e9a7faba1022f9704ea0499c2366e4c836107782',
    ('v11', 'contact'): 'd837fbe1bfae151cb2b56c2a1fc780ba621f0e1665de089483d5a537c809f728',
    ('v13', 'group'): 'dfcb98ae3de61c4d48890a5252f9ae0a2acad23c0c72e5b75f88aea8759cf8e8',
    ('v13', 'contact'): '3dd714c12991003e5c5d5996c2f99f7354b4ef13067fa031d110de8660ddeab8',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root=ROOT):
    base = root / 'docs/quartic-318-326'
    decisions = {}
    for (version, who), digest in DECISIONS.items():
        folder = base / (version + '-consumer-binding')
        path = folder / 'decisions' / who / 'acceptance.json'
        assert sha(path) == digest, f'Changed independent decision: {version}/{who}'
        decision = json.loads(path.read_text())
        app = decision['application']['sha256'] if version == 'v11' and who == 'group' else decision['application_sha256']
        candidate = decision['candidate_manifest']['sha256'] if version == 'v11' and who == 'group' else decision['candidate_manifest_sha256']
        assert sha(folder / 'APPLICATION.json') == app, 'Stale application acceptance'
        assert sha(folder / 'candidate-manifest.json') == candidate, 'Stale candidate acceptance'
        for name, expected in json.loads((folder / 'candidate-manifest.json').read_text())['files'].items():
            assert sha(folder / name) == expected, f'Changed reviewed artifact: {version}/{name}'
        decisions[version, who] = decision
    v11 = {row['target']: row['sha256'] for row in decisions['v11', 'group']['accepted_outputs']}
    assert v11 == decisions['v11', 'contact']['proposed_consumers']
    v13 = {row['target']: row for row in decisions['v13', 'group']['outputs']}
    contact = {row['target']: row for row in decisions['v13', 'contact']['proposed_outputs']}
    assert set(v11) == set(v13) == set(contact)
    for target, row in v13.items():
        assert row['before_sha256'] == v11[target] == contact[target]['before_sha256'], 'Broken historical chain'
        assert row['after_sha256'] == contact[target]['after_sha256'] == sha(root / target), f'Unreviewed current consumer: {target}'
        name = contact[target]['candidate_file']
        assert sha(base / 'v13-consumer-binding' / name) == row['after_sha256']
    historical = base / 'v11-consumer-binding/arithmetic-obligations.before.md'
    old = json.loads((root / 'quartics/quartic-318-326/proof/components/verification.json').read_text())['sha256']['arithmetic-obligations.md']
    assert sha(historical) == old, 'Original component receipt lost its historical prose binding'
    return historical

if __name__ == '__main__':
    verify()
    print('PASS: exact reviewed V10 -> V11 -> V13 consumer bindings; historical Lean receipt unchanged.')
