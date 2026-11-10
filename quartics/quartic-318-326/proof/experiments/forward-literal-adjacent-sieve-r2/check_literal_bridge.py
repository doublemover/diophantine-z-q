#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-literal-adjacent-sieve-r1"/"check_literal_bridge.py"),run_name="__main__")
