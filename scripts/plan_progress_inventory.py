#!/usr/bin/env python3
"""Exact-source, dependency-closed inventory plan. No compiler or binary reuse."""
import argparse
import hashlib
import json
from pathlib import Path
import check_progress_experiment as experiment
import check_progress_lean as ci
import validate_progress_inventory_request as request


def selection(packet, intake_sha256, data, targets):
    order = data['order']
    names = set(order)
    if targets is not None:
        if (not isinstance(targets, list) or not targets or
            any(not isinstance(n, str) for n in targets) or len(set(targets)) != len(targets) or
            not set(targets) <= names):
            raise ValueError('Invalid or unknown inventory target')
    chosen = names if targets is None else set(targets)
    closure = set(chosen)
    todo = list(chosen)
    while todo:
        name = todo.pop()
        for dep in set(data['files'][name + '.lean']['imports']) & names:
            if dep not in closure:
                closure.add(dep); todo.append(dep)
    selected_order = [n for n in order if n in closure]
    identity = {'packet': packet, 'intake_sha256': intake_sha256,
                'targets': None if targets is None else [n for n in order if n in chosen],
                'selected_order': selected_order}
    identity['selection_sha256'] = hashlib.sha256(
        json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return identity


def build(request_data, plan, active, packet_fn=experiment.packet,
          publication_fn=experiment.check_application_publication):
    request.validate_shape(request_data)
    if (not isinstance(active, list) or len(active) > 16 or
        any(not isinstance(n, str) for n in active) or len(set(active)) != len(active)):
        raise ValueError('Invalid active experiment matrix')
    shards = ([{'packet': n, 'targets': None} for n in active]
              if request_data['schema'] == 1 else request_data['shards'])
    minutes = 30 if request_data['schema'] == 1 else request_data['job_minutes']
    packets = {}
    for name in dict.fromkeys(s['packet'] for s in shards):
        if name not in active:
            raise ValueError('Shard packet is not active at this exact source head: ' + name)
        # Full source/import/binding validation precedes narrowing to a closure.
        packets[name] = packet_fn(name, plan)
    publication_fn([item[0] for item in packets.values()])
    rows = []
    for shard in shards:
        name = shard['packet']; folder, data, _, _ = packets[name]
        chosen = selection(name, ci.sha(folder / 'intake.json'), data, shard['targets'])
        key = name if request_data['schema'] == 1 else name + '-s' + chosen['selection_sha256'][:16]
        rows.append({'packet': name, 'artifact_key': key,
                     'targets_json': json.dumps(chosen['targets'], separators=(',', ':')),
                     'selection_sha256': chosen['selection_sha256'],
                     'job_minutes': minutes, 'window_minutes': minutes - 6})
    if len({r['artifact_key'] for r in rows}) != len(rows):
        raise ValueError('Shard artifact identity collision')
    return {'matrix': {'include': rows}, 'base': plan['base'], 'snapshot': plan['snapshot'],
            'has_packets': 'true' if rows else 'false'}


def main():
    if not __debug__:
        raise RuntimeError('Do not use Python -O')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--github-output', required=True, type=Path)
    p.add_argument('--baseline-upstream-targets', type=Path)
    args = p.parse_args()
    # Revalidate committed marker and clean execution tree, not an editable JSON receipt.
    import os
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    validated = request.validate(ci.ROOT, event, os.environ)
    raw = json.loads((ci.ROOT / request.MARKER).read_text(), object_pairs_hook=request.unique_object)
    ci.check_sources(ci.PROJECT)
    plan = ci.derive_plan(early_depth=7)
    from prepare_progress_sparse_checkout import EXPERIMENTS, read_json
    active = read_json(ci.ROOT, validated['execution_commit'],
                       EXPERIMENTS + '/packets.json')['active_packets']
    result = build(raw, plan, active)
    if args.baseline_upstream_targets is not None and result['has_packets'] == 'true':
        # Stable common seed. Packet-specific imports remain native per-job
        # lookups so a proof edit cannot invalidate the shared baseline cache.
        targets = sorted({n for n in plan['upstream']
                          if n.split('.')[0] not in {'Lean', 'Std', 'Init'}})
        if not targets:
            raise ValueError('Expected nonempty baseline upstream targets')
        encoded = ('\n'.join(targets) + '\n').encode()
        args.baseline_upstream_targets.write_bytes(encoded)
        result['baseline_upstream_targets_sha256'] = hashlib.sha256(encoded).hexdigest()
    print(json.dumps({'request_sha256': validated['marker_sha256'], **result}))
    with args.github_output.open('a') as f:
        for k, v in result.items():
            f.write(k + '=' + (json.dumps(v, separators=(',', ':')) if isinstance(v, dict) else v) + '\n')


if __name__ == '__main__':
    main()
