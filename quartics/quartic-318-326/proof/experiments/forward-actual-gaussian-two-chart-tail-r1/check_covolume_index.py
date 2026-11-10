#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-gaussian-source-rankin-r2"/"check_covolume_index.py"),run_name="__main__")
