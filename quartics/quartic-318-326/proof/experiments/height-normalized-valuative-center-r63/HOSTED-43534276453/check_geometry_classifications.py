"""Source-only intake delta check. Never invokes Lean/Lake or changes a repository."""
import argparse
import copy
import json
from pathlib import Path

PAIRS = [
    ('height-normalized-valuative-center-r58', 'height-normalized-valuative-center-r59'),
    ('height-original-ks-lattice-assembly-r9', 'height-original-ks-lattice-assembly-r10'),
]

def check(data, expected):
    for key, value in expected.items():
        if data.get(key) != value:
            raise ValueError('Ancillary intake mismatch: ' + key)
    groups = [set(data[k]) for k in ['new_modules', 'revised_modules', 'reused_modules']]
    if set.union(*groups) != set(data['order']):
        raise ValueError('Ancillary categories do not cover module order')
    if any(groups[i] & groups[j] for i in range(3) for j in range(i)):
        raise ValueError('Ancillary categories overlap')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--successors', type=Path, required=True)
    args = ap.parse_args()
    for old, new in PAIRS:
        before = args.repo / 'quartics/quartic-318-326/proof/experiments' / old
        after = args.successors / new
        d = json.loads((after / 'intake.json').read_text())
        p = json.loads((before / 'intake.json').read_text())
        assert d['order'] == p['order']
        assert set(d['files']) == set(p['files'])
        revised = [n for n in d['order'] if
                   (before / (n + '.lean')).read_bytes() != (after / (n + '.lean')).read_bytes()]
        reused = [n for n in d['order'] if n not in revised]
        expected = dict(new_modules=[], revised_modules=revised,
                        reused_modules=reused, unchanged_predecessor_modules=reused)
        check(d, expected)
        controls = 0
        for key in ['new_modules', 'revised_modules', 'reused_modules', 'unchanged_predecessor_modules']:
            bad = copy.deepcopy(d)
            bad[key] = ['__unexpected__'] if key == 'new_modules' else []
            try:
                check(bad, expected)
            except ValueError:
                controls += 1
            else:
                raise AssertionError('Failed negative control: ' + key)
        print(json.dumps(dict(packet=new, result='PASS', revised=revised,
                              reused=len(reused), rejected_negative_controls=controls)))

if __name__ == '__main__':
    main()
