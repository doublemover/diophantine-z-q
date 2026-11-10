#!/usr/bin/env python3
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent.parent/"forward-literal-basis-polynomials-r1"/"check_ternary_lattices.py"),run_name="__main__")
