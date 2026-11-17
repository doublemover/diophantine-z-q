#!/usr/bin/env python3
"""Read-only verification of archived integration identities, never Lean acceptance."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

EXPERIMENTS = 'quartics/quartic-318-326/proof/experiments/'
HEX40 = re.compile(r'[0-9a-f]{40}')
HEX64 = re.compile(r'[0-9a-f]{64}')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def validate(repo, checkpoint):
    """Only git show/rev-parse/merge-base; no fetch, checkout, writes, or network."""
    def git(*args):
        return subprocess.check_output(['git', '-C', str(repo), *args], stderr=subprocess.PIPE)
    def text(*args):
        return git(*args).decode().strip()
    def oid(value):
        require(isinstance(value, str) and HEX40.fullmatch(value), 'invalid object identifier')
        return value
    def ancestor(commit, anchor):
        result = subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', oid(commit), anchor], capture_output=True)
        require(result.returncode == 0, 'recorded source cut is not an ancestor of anchor')

    require(checkpoint.get('schema') == 'integration-recovery-v1', 'unsupported schema')
    require(checkpoint.get('runtime_acceptance') is False, 'checkpoint must not claim runtime acceptance')
    anchor = oid(checkpoint['source_anchor']['commit'])
    require(text('rev-parse', anchor + '^{tree}') == oid(checkpoint['source_anchor']['tree']), 'anchor tree mismatch')
    registry_raw = git('show', anchor + ':' + EXPERIMENTS + 'packets.json')
    require(sha(registry_raw) == checkpoint['registry_sha256'], 'registry hash mismatch')
    active = json.loads(registry_raw)['active_packets']
    rows = checkpoint['active_packets']
    require([r['name'] for r in rows] == active, 'active packet order mismatch')
    require(len(active) == 16 and len(set(active)) == 16, 'active packet count or uniqueness mismatch')
    for row in rows:
        name = row['name']
        require(re.fullmatch(r'[A-Za-z0-9_-]+', name), 'invalid packet path')
        require(text('rev-parse', anchor + ':' + EXPERIMENTS + name) == oid(row['tree']), 'packet subtree mismatch')

    records = checkpoint['receipts']
    require(records and len({r['name'] for r in records}) == len(records), 'empty or duplicate receipts')
    kinds = {'serial', 'constituent', 'publication', 'helper'}
    by_hash = {r['sha256']: r for r in records}
    for record in records:
        require(record['kind'] in kinds, 'unknown receipt kind')
        require(HEX64.fullmatch(record['sha256']), 'invalid receipt hash')
        raw = record['raw_utf8'].encode()
        require(sha(raw) == record['sha256'], 'receipt bytes mismatch')
        data = json.loads(raw)
        if record['kind'] == 'publication':
            require(data['status'] in ('PUBLISHED_REMOTE_VERIFIED', 'ALREADY_PUBLISHED_REMOTE_VERIFIED'), 'publication status not verified')
            require(data['remote'] == data['commit'], 'publication readback mismatch')
            review = by_hash.get(data['review_sha256'])
            require(review is not None and review['kind'] == 'serial', 'publication review missing')
            require(json.loads(review['raw_utf8'])['commit'] == data['commit'], 'publication review commit mismatch')
        else:
            require(str(data.get('status', '')).startswith('PASS'), 'review status not PASS')
        if record['kind'] in ('serial', 'publication'):
            commit = oid(data['commit'])
            ancestor(commit, anchor)
            require(text('rev-parse', commit + '^{tree}') == oid(data['tree']), 'receipt tree mismatch')
            require(text('show', '-s', '--format=%P', commit) == oid(data['parent']), 'receipt parent mismatch')
            if record['kind'] == 'serial':
                marker = '.github/inventory-requests/progress.json'
                require(git('show', commit + ':' + marker) == git('show', data['parent'] + ':' + marker), 'serial changed marker')
                for file in data.get('files', []):
                    path = file['path']
                    require(not path.startswith('/') and all(x not in ('', '.', '..') for x in path.split('/')), 'invalid serial file path')
                    require(sha(git('show', commit + ':' + path)) == file['sha256'], 'serial file mismatch')
                    if file['previous_sha256'] is not None:
                        require(sha(git('show', data['parent'] + ':' + path)) == file['previous_sha256'], 'serial file preimage mismatch')
                    else:
                        require(git('ls-tree', '-z', data['parent'], '--', path) == b'', 'new serial file exists in parent')
                for packet in data.get('packets', []):
                    require(re.fullmatch(r'[A-Za-z0-9_-]+', packet['new']), 'invalid serial packet path')
                    require(text('rev-parse', commit + ':' + EXPERIMENTS + packet['new']) == oid(packet['sha']), 'serial graft mismatch')
        if record['kind'] == 'constituent':
            # Local constituent commits may not survive a rollback. The accepted packet
            # subtree and raw receipt remain archived; do not claim the full local tree.
            binding = record.get('reachable_packet')
            if binding:
                require(re.fullmatch(r'[A-Za-z0-9_-]+', binding['name']), 'invalid constituent packet path')
                expected = data.get('packet_subtree', binding['tree'])
                require(expected == oid(binding['tree']), 'constituent receipt subtree mismatch')
                require(text('rev-parse', anchor + ':' + EXPERIMENTS + binding['name']) == expected, 'constituent packet not reachable')
    return {'status': 'PASS_READ_ONLY_SOURCE_RECOVERY_IDENTITIES_NOT_LEAN', 'source_anchor': anchor,
            'active_packets': len(rows), 'receipts': len(records), 'runtime_acceptance': False,
            'limitations': ['Historical remote readback is archived evidence, not a new remote query.',
                           'PASS here does not authenticate proof compilation, runtime audits, or unresolved mathematical premises.',
                           'Only serial commits and packet subtrees are required reachable; lost local constituent history is not fabricated.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True)
    parser.add_argument('checkpoint')
    args = parser.parse_args()
    print(json.dumps(validate(args.repo, json.loads(Path(args.checkpoint).read_text())), indent=2))


if __name__ == '__main__':
    main()
