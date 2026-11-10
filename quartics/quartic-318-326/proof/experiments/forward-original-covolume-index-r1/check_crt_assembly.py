#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-attained-minima-r1"/"check_crt_assembly.py"),run_name="__main__")
