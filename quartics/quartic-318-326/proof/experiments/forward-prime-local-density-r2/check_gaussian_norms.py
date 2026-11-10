#!/usr/bin/env python3
"""Preserve predecessor-bound tests; new source repair checked separately."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/'forward-prime-local-density-r1'/'check_gaussian_norms.py'),run_name='__main__')
