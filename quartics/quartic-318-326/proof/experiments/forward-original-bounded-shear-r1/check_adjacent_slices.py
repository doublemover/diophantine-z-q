#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-affine-prime-support-r1"/"check_adjacent_slices.py"),run_name="__main__")
