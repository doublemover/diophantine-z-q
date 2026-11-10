#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-controlled-basis-r2"/"check_good_basis.py"),run_name="__main__")
