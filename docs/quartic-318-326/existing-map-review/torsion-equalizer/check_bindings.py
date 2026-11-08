#!/usr/bin/env python3
"""Verify source bindings only. This is not a Lean replay or semantic prover."""
import hashlib,json,pathlib,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
REPO=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else '/workspace/scratch/2cb21e4e0864/diophantine-z-q')
d=json.loads((HERE/'BINDINGS.json').read_text()); checked=0
for f in d['files']:
 p=REPO/f['path']; actual=hashlib.sha256(p.read_bytes()).hexdigest()
 assert actual==f['sha256'],(f['path'],actual,f['sha256'])
 if f.get('producer_sha256'):assert actual==f['producer_sha256'],f['path']
 checked+=1
changes=subprocess.check_output(['git','diff','--name-only',d['ci_source_commit'],d['reviewed_commit'],'--','quartics/quartic-318-326/proof/progress/*.lean'],cwd=REPO,text=True)
assert not changes,changes
result={'status':'passed','scope':'exact file/producer hash checks and CI-to-review Lean source equality only','bound_files':checked,'primary_lean_sources':d['primary_lean_source_count'],'local_lean_replay':False,'semantic_correctness_decided_by_this_script':False,'ci_to_review_progress_lean_changes':[]}
print(json.dumps(result,indent=2))
