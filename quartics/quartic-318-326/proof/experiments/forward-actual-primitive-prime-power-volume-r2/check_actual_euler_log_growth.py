#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-ambient-primitive-lifts-r1"/"check_actual_euler_log_growth.py"),run_name="__main__")
