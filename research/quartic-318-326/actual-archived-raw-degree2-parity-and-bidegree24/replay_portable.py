from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys

root = Path(__file__).resolve().parent
inputs = root/'input'
src = root/'author'/'bidegree24'
with TemporaryDirectory() as tmp:
    layout = Path(tmp)
    runner = layout/'rc-native-helper-20261120'/'ct-original-raw-bidegree24-obstruction-r1'
    older = layout/'high-hom-1120'/'heegner-compressed-trace'/'original-a0-factorless-companion-norm-line-r1'
    sharp = older.parent/'original-linear-q-a0-exact-anchor-depth-full-scalar-r1'
    for d in (runner, older, sharp):
        d.mkdir(parents=True)
    script = runner/'check_bidegree24_fixed_classes_and_rows.py'
    script.write_bytes((src/script.name).read_bytes())
    for name,dest in (('PINNED-SCALAR-FIBER.json',older),
                      ('EXACT-A0-FULL-SCALAR-ANCHOR-DEPTH.json',sharp)):
        (dest/name).write_bytes((inputs/name).read_bytes())
    (sharp/'SHA256SUMS').write_bytes((inputs/'UPSTREAM-SHARP-SHA256SUMS.txt').read_bytes())
    out = subprocess.check_output([sys.executable,'-B',str(script)])
    assert out == (src/'EXACT-BIDEGREE24-FIXED-CLASSES-ROWS.json').read_bytes()
print('PASS: exact archived input depths and four combined-fibre coefficient rows')
