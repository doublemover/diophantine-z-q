#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-reduced-sieve-inputs-r1"/"check_dual_incidence.py"),run_name="__main__")
