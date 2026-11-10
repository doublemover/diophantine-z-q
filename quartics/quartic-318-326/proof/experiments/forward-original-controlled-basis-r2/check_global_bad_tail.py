#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-global-bad-tail-r2"/"check_global_bad_tail.py"),run_name="__main__")
