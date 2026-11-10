#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-quartic-rectangle-tail-r1"/"check_original_bases.py"),run_name="__main__")
