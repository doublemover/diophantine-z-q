#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-character-boundary-lower-r1"/"check_local_residue_bounds.py"),run_name="__main__")
