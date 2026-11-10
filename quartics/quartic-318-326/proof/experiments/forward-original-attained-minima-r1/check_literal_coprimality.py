#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-original-full-lattices-r1"/"check_literal_coprimality.py"),run_name="__main__")
