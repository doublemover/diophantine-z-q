#!/usr/bin/env python3
"""Normalize download-artifact's singleton layout without changing bundle bytes.

The pinned download action flattens a pattern download when exactly one artifact
matches. The existing proof verifier requires progress-cohort-<id>/ in both the
single- and multiple-artifact cases. It remains responsible for all admission.
"""
import argparse
import json
from pathlib import Path
import shutil


def normalize(root):
    root = Path(root)
    receipt = root / 'receipt.json'
    if not receipt.exists():
        return False  # Multi-artifact layout, or missing inputs: verifier decides.
    row = json.loads(receipt.read_text())
    cohort = row.get('cohort')
    if type(cohort) is not int or cohort < 0 or row.get('status') != 'PASS':
        raise ValueError('Flat download is not a successful cohort bundle')
    if any(p.name.startswith('progress-cohort-') for p in root.iterdir()):
        raise ValueError('Mixed singleton/nested artifact layouts')
    target = root / f'progress-cohort-{cohort}'
    children = list(root.iterdir())
    target.mkdir()
    for child in children:
        shutil.move(str(child), target / child.name)
    return True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    print('Normalized singleton cohort download' if normalize(args.directory) else 'Nested cohort layout retained')
