#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-anisotropic-coordinates-r1"/"check_bad_mass.py"),run_name="__main__")
