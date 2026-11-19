"""Cold, local, no network. Requires Python 3 and SymPy for independent symbolic rational check."""
from tempfile import TemporaryDirectory
from pathlib import Path
import subprocess,sys,json,hashlib,shutil
P=Path(__file__).resolve().parent
def h(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def run(f,*args):subprocess.run([sys.executable,'-IB',str(f),*(str(a)for a in args)],check=True,cwd=P)
assert all(h(P/n)==v for n,v in json.loads((P/'SHA256SUMS.json').read_text()).items())
run(P/'verify.py');run(P/'review.py',P,P/'donor180',P/'scalar181')
with TemporaryDirectory()as tmp:
 r=Path(tmp);dst=r/'practical180';dst.mkdir();(dst/'proposal').mkdir();shutil.copyfile(P/'build.py',dst/'build.py');shutil.copytree(P/'donor180',r/'effective180');run(dst/'build.py')
 for f in (dst/'proposal').iterdir():assert (P/f.name).read_bytes()==f.read_bytes(),f.name
print('PASS both independent checks and exact isolated compiler reproduction.')
