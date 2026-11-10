#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-full-shear-rectangle-r2"/"check_small_prime_tail.py"),run_name="__main__")
