#!/usr/bin/env python3
"""Fail-closed marker-only feature-branch launch; no compiler or network calls."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

BRANCH = 'refs/heads/add-quartic-318-326'
MARKER = '.github/inventory-requests/progress.json'


def git(root, *args):
    return subprocess.check_output(['git', '--no-replace-objects', *args], cwd=root)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate request key: '+key)
        result[key] = value
    return result


def validate(root, event, env):
    if env.get('GITHUB_EVENT_NAME') != 'push' or env.get('GITHUB_REF') != BRANCH:
        raise ValueError('Only the explicit feature-branch push route is permitted')
    if event.get('ref') != BRANCH or event.get('deleted') is not False or event.get('forced') is not False:
        raise ValueError('Unexpected branch, deletion or force push')
    head = env.get('GITHUB_SHA', '')
    if not re.fullmatch('[0-9a-f]{40}', head) or event.get('after') != head:
        raise ValueError('Event/head identity mismatch')
    if git(root, 'rev-parse', 'HEAD').decode().strip() != head:
        raise ValueError('Checkout is not the exact event commit')
    # Both comparisons are required: staged changes can be undone only in the
    # worktree, leaving an otherwise invisible different index.
    try:
        git(root, 'diff', '--no-ext-diff', '--no-textconv', '--quiet', 'HEAD', '--')
        git(root, 'diff', '--cached', '--no-ext-diff', '--no-textconv', '--quiet', 'HEAD', '--')
    except subprocess.CalledProcessError as error:
        raise ValueError('Tracked worktree or index differs from the execution commit') from error
    raw = (root / MARKER).read_bytes()
    if len(raw) > 4096 or git(root, 'show', head+':'+MARKER) != raw:
        raise ValueError('Request is oversized or not the committed bytes')
    tree_entry = git(root, 'ls-tree', head, '--', MARKER).decode()
    if not tree_entry.startswith('100644 blob '):
        raise ValueError('Request must be an ordinary nonexecutable tracked file')
    request = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(request, dict) or set(request) != {'schema','source_commit','source_tree','request_id'}:
        raise ValueError('Unexpected request schema')
    if type(request['schema']) is not int or request['schema'] != 1:
        raise ValueError('Unsupported request schema')
    source, source_tree = request['source_commit'], request['source_tree']
    if any(not isinstance(x,str) or not re.fullmatch('[0-9a-f]{40}',x) for x in (source,source_tree)):
        raise ValueError('Request requires full immutable commit/tree IDs')
    if not isinstance(request['request_id'],str) or not re.fullmatch('[A-Za-z0-9_-]{1,64}',request['request_id']):
        raise ValueError('Invalid request ID')
    parents = git(root, 'show', '-s', '--format=%P', head).decode().split()
    if parents != [source] or event.get('before') != source:
        raise ValueError('Push must contain exactly one marker-only commit after the published requested source')
    if git(root, 'rev-parse', source+'^{tree}').decode().strip() != source_tree:
        raise ValueError('Requested source tree does not match source commit')
    changed = git(root, 'diff-tree', '--no-commit-id', '--name-only', '-r', '-z', source, head).split(b'\0')
    if [p for p in changed if p] != [MARKER.encode()]:
        raise ValueError('Launch commit changes something other than the request marker')
    return {'status':'VALIDATED_MARKER_ONLY_REQUEST', **request, 'execution_commit':head,
            'execution_tree':git(root,'rev-parse',head+'^{tree}').decode().strip(),
            'marker_sha256':hashlib.sha256(raw).hexdigest(),
            'unchanged_non_marker_tree':True, 'proof_acceptance':False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--github-output',required=True,type=Path)
    args=p.parse_args()
    event=json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    result=validate(Path(__file__).resolve().parents[1],event,os.environ)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    with args.github_output.open('a') as f:
        for key in ('source_commit','source_tree','marker_sha256'):
            f.write(key+'='+result[key]+'\n')


if __name__=='__main__':
    main()
