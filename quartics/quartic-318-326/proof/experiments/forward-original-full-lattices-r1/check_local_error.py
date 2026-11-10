#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-euclidean-dual-r1"/"check_local_error.py"),run_name="__main__")
