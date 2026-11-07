"""Generate both quartics; optionally compare the published coefficient tables."""

from pathlib import Path
import argparse
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE_318 = Path("construction/318")
SOURCE_326 = Path("construction/326")
RESULT_318 = Path("results/318")
RESULT_326 = Path("results/326")


def run(root, *args):
    subprocess.run(
        [str(x) for x in args], cwd=root, check=True, stdout=subprocess.DEVNULL
    )


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=ROOT / "build/results")
parser.add_argument(
    "--check",
    action="store_true",
    help="Compare generated coefficient tables with results/ instead of writing output",
)
args = parser.parse_args()

with tempfile.TemporaryDirectory(prefix="quartic-generate-") as directory:
    work = Path(directory)
    for relative in (SOURCE_318, SOURCE_326, Path("tools")):
        (work / relative).mkdir(parents=True)
        for source in (ROOT / relative).glob("*"):
            if source.suffix in (".py", ".cjs"):
                shutil.copyfile(source, work / relative / source.name)
    for relative in (RESULT_318, RESULT_326, Path("docs/sources")):
        (work / relative).mkdir(parents=True)
    manuscript = Path("docs/sources/diophantine_optimization_20261106_v3.tex")
    shutil.copyfile(ROOT / manuscript, work / manuscript)
    run(work, "node", SOURCE_318 / "build_source.cjs")
    compiler = Path("tools/compile.py")
    run(
        work,
        sys.executable,
        compiler,
        SOURCE_318 / "raw-translated-ir.json",
        SOURCE_318 / "compiled",
        "--no-reduce",
    )
    run(work, sys.executable, SOURCE_318 / "shear.py")
    run(
        work,
        sys.executable,
        compiler,
        SOURCE_318 / "sheared-ir.json",
        RESULT_318,
        "--no-reduce",
    )
    run(work, sys.executable, SOURCE_318 / "export_coefficients.py")
    run(work, sys.executable, SOURCE_326 / "lift.py")
    run(
        work,
        sys.executable,
        compiler,
        SOURCE_326 / "lifted-ir.json",
        RESULT_326,
        "--no-reduce",
    )
    run(work, sys.executable, SOURCE_326 / "export_coefficients.py")
    if args.check:
        for relative in (
            RESULT_318 / "polynomial.json",
            RESULT_318 / "coefficients.json",
            RESULT_318 / "coefficients.txt",
            RESULT_326 / "polynomial.json",
            RESULT_326 / "coefficients.txt",
        ):
            if (work / relative).read_bytes() != (ROOT / relative).read_bytes():
                raise RuntimeError(f"Generated coefficients differ: {relative}")
        print("Both coefficient tables match results/.")
    else:
        shutil.copytree(work / "results", args.output, dirs_exist_ok=True)
        print(f"Generated both quartics in {args.output}")
