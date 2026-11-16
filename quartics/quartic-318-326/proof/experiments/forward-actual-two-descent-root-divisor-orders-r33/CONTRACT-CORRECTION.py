from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent; rows=json.loads((B/'PROPOSED-DESCENT.json').read_text());row=rows[0];p=Path(row['source']);hist=p/'CURRENT-CONTRACT-HISTORY'/'INITIAL-WEIGHTED-CANONICAL-WORDING';assert not hist.exists();hist.mkdir(parents=True)
H=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
oldapp=H(p/'APPLICATION.json')
for n in ['APPLICATION.json','APPLICATION.md']:shutil.copy2(p/n,hist/n)
shutil.copy2(B/'PROPOSED-DESCENT.json',hist/'PROPOSED-DESCENT.json')
app=json.loads((p/'APPLICATION.json').read_text());clause=next(x for x in app['obligations'] if x['id']=='dependency_chase')
for field in ['required_input','constructed_input']:
 t=clause[field];assert 'weighted32' in t and 'fails1.468s' in t
 clause[field]=t.replace('weighted32','descent32').replace('fails1.468s','fails1.920s')
md=(p/'APPLICATION.md').read_text();assert md.count('weighted32 has117')==1 and md.count('fails1.468s')==1
(p/'APPLICATION.md').write_text(md.replace('weighted32 has117','descent32 has117').replace('fails1.468s','fails1.920s'))
(p/'CONTRACT-CORRECTION.md').write_text('# Current own-receipt correction\n\nThe first descent33 current dependency_chase clause repeated weighted32 canonical receipt wording (1.468s). Its own receipt and justification already correctly identified descent32 (1.920s). The current required_input/constructed_input and APPLICATION.md now identify the separately authenticated descent32 receipt:117 complete passes, then PreparedAnchorSource318 fails1.920s;1181 roots unreached. This is a current-evidence attribution correction only. Source, intake, assumptions, budgets, own receipt and weighted33 are unchanged.\n\nThe exact initial descent APPLICATION.json/md and map are preserved under CURRENT-CONTRACT-HISTORY/INITIAL-WEIGHTED-CANONICAL-WORDING. Initial APP SHA256 '+oldapp+'. Frozen weighted-only canonical history remains unchanged and must not be mistaken for descent own evidence. This correction needs fresh independent current review.\n')
shutil.copy2(Path(__file__),p/'CONTRACT-CORRECTION.py')
app['bindings']={str(q.relative_to(p)):H(q) for q in p.rglob('*') if q.is_file() and (q.parent!=p or q.name in ['README.md','APPLICATION.md','COPY-BINDINGS.json','CONTRACT-CORRECTION.md','CONTRACT-CORRECTION.py'])}
(p/'APPLICATION.json').write_text(json.dumps(app,indent=2)+'\n');row['application_sha256']=H(p/'APPLICATION.json');(B/'PROPOSED-DESCENT.json').write_text(json.dumps(rows,indent=2)+'\n')
print('previous',oldapp);print('current',row['application_sha256']);print('intake unchanged',H(p/'intake.json'));print('bindings',len(app['bindings']))
