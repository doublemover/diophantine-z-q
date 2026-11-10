#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-weighted-bad-slices-r1"/"check_prime_local_counts.py"),run_name="__main__")
