#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-good-point-sieve-r2"/"check_minimum_tail.py"),run_name="__main__")
