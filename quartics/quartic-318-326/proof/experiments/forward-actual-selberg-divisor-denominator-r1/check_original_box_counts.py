#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-actual-selberg-euler-truncation-r2"/"check_original_box_counts.py"),run_name="__main__")
