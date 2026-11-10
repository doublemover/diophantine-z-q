#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-large-prime-point-fibers-r1"/"check_good_point_tail.py"),run_name="__main__")
