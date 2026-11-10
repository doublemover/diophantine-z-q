#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-gaussian-full-source-tail-r1"/"check_transference.py"),run_name="__main__")
