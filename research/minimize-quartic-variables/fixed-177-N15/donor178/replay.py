from pathlib import Path
import hashlib,sys,json,subprocess
D=Path(__file__).resolve().parent
mf=json.loads((D/'SHA256SUMS.json').read_bytes())
for k,v in mf.items():assert hashlib.sha256((D/k).read_bytes()).hexdigest()==v,k
def run(f,*a):subprocess.run([sys.executable,'-IB',str(D/f),*[str(i)for i in a]],cwd=D,check=True)
run('build.py');run('numerics.py');run('independent-check.py',D,D/'donor')
print('PASS practical 178 at N=15; three proof/source replays.')
