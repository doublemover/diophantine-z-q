from pathlib import Path
import hashlib,json
root=Path('/workspace/scratch/2cb21e4e0864'); repo=root/'diophantine-z-q'; out=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
d=json.loads((out/'evidence.json').read_text())
for e in d['evidence']:
 b=(repo/e['path']).read_bytes(); ls=b.splitlines(keepends=True)
 assert sha(b)==e['file_sha256'],e['id']+' whole file changed'
 assert 1<=e['start_line']<=e['end_line']<=len(ls),e['id']+' invalid lines'
 assert sha(b''.join(ls[e['start_line']-1:e['end_line']]))==e['excerpt_sha256'],e['id']+' passage changed'
for s in d['sources']:
 f=out/s['file']; assert sha(f.read_bytes())==s['sha256'],s['id']+' source changed'
 pages=f.with_suffix('.txt').read_bytes().split(b'\x0c')
 for e in s['source_passages']: assert sha(pages[e['pdf_page_1_based']-1])==e['extracted_page_sha256']
for e in d['web_version_evidence']: assert sha((out/e['path']).read_bytes())==e['sha256']
for a in d['applications']:
 assert len(a['obligations'])==9
 assert len({x['obligation'] for x in a['obligations']})==9
 for x in a['obligations']:
  assert all(x[k] for k in ('required','constructed_or_proved','why_match_or_remaining','evidence','status'))
  assert all(ref in {z['id'] for z in d['evidence']} for ref in x['evidence'])
assert sha((repo/'manuscripts/quartic_v11.tex').read_bytes())==d['v11_contract_sha256']
print('PASS: 33 project passages, 5 source files, 3 web-version files, and 45 obligation-row bindings. Structural integrity only; no mathematical acceptance or inventory-completeness claim.')
