#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-ternary-lattice-cover-r2"/"check_euler_correction.py"),run_name="__main__")
