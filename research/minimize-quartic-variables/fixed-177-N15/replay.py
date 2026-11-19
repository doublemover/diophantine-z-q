"""One-command portable source and coefficient replay. No network, writes, or subprocess package installation."""
import sys,subprocess,json,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent
mf=json.loads((D/'SHA256SUMS.json').read_bytes())
for f,h in mf.items(): assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
def run(f):subprocess.run([sys.executable,'-IB',str(D/f)],cwd=D,check=True)
run('donor178/replay.py');run('build.py');run('arithmetic.py');run('literal_check.py')
if '--sympy' in sys.argv:run('recheck.py')
print('PASS fixed 177 offline replay; conditional suppliers are not certified by coefficient checks.')
