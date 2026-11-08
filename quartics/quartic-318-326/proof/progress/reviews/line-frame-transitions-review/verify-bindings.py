from pathlib import Path
import hashlib,json
b=Path(__file__).resolve().parents[2]
r=json.loads(Path(__file__).with_name('BINDINGS.json').read_text())
for x in r['bindings']:
 p=b/x['path']; assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'],x['path']
print('BINDINGS_PASS',len(r['bindings']))
