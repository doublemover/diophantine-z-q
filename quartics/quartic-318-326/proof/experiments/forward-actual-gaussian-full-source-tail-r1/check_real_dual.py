#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-gaussian-zero-stratum-r2"/"check_real_dual.py"),run_name="__main__")
