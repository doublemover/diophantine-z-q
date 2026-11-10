#!/usr/bin/env python3
"""Run the immutable predecessor tests against their original bound packet.
The successor's own checker verifies every copied Lean source byte-for-byte.
"""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent /
 'forward-conjugate-count-selection-r2' / 'check_conjugate_counts.py'),run_name='__main__')
