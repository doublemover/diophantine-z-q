from pathlib import Path
import hashlib,json,sys,subprocess
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'geometry-ks54-open-localization-integration';P=R/'quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r54';B=R/'quartics/quartic-318-326/proof/progress'
sys.path.insert(0,str(R/'scripts'));from check_progress_lean import import_names
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source='afaf006589eaf71fddcaa88f5d688d996d4ecb68';prefix='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r54'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
assert git('rev-parse',source+':'+prefix).decode().strip()=='34a199f3df61229b621593c5e611c5abf9942a55'
intake=json.loads((P/'intake.json').read_text());base=json.loads((B/'checkpoint-manifest.json').read_text());baseline=set(base['module_order']);paths={n:P/(n+'.lean') for n in intake['order']}
target='OriginalIntegerClosureGluing318';paths[target]=W/'geometry-reciprocal-normalization/sources'/f'{target}.lean';manifest=W/'geometry-reciprocal-normalization/MANIFEST.json';assert H(paths[target])==json.loads(manifest.read_text())['sources'][target+'.lean']
order=[];seen=set();bo=[];bs=set();visiting=set()
def walk(n):
 if n.startswith(('Mathlib.','Lean.','Std.','Batteries.')):return
 if n in baseline:
  if n in bs:return
  q=B/(n.replace('.','/')+'.lean');assert H(q)==base['modules'][n]['sha256']
  for d in sorted(import_names(q.read_text())):walk(d)
  bs.add(n);bo.append(n);return
 if n in seen:return
 assert n in paths,n;assert n not in visiting,n;visiting.add(n)
 for d in sorted(import_names(paths[n].read_text())):walk(d)
 visiting.remove(n);seen.add(n);order.append(n)
walk(target);assert len(order)==53 and len(bo)==180
host=W/'hosted-monitor-43975754875/ks52';inv=json.loads((host/'INVENTORY.json').read_text());auth=W/'resume-independent-review/KS54-N2-FIFTYTWO-HOSTED-43975754875-ASTRA-REVIEW.json';av=json.loads(auth.read_text());assert set(order)-{target}==set(av['passed_modules']);passed={}
for n in order:
 if n==target:continue
 sha=H(paths[n]);assert sha==intake['files'][n+'.lean']['sha256'];assert hashlib.sha256(git('show',source+':'+prefix+'/'+n+'.lean')).hexdigest()==sha;passed[n]=sha
bindings={str(paths[n].relative_to(W)):H(paths[n]) for n in order}
for n in bo:q=B/(n.replace('.','/')+'.lean');bindings[str(q.relative_to(W))]=H(q)
for q in [manifest,P/'intake.json',B/'checkpoint-manifest.json',host/'INVENTORY.json',host/'BINDING-VERIFIED.json',auth,W/'resume-independent-review/RECIPROCAL-NORMALIZATION-GLUING-ASTRA-REVIEW.json']:bindings[str(q.relative_to(W))]=H(q)
v=dict(status='DEPENDENCY_REBASE_CANDIDATE_NOT_NEW_LEAN_ACCEPTANCE',passed_source_commit=source,passed_packet=P.name,passed_packet_subtree='34a199f3df61229b621593c5e611c5abf9942a55',target=target,draft_dependency_order=order,baseline_dependency_order=bo,draft_closure_count=len(order),baseline_closure_count=len(bo),new_sources=[dict(module=target,path=str(paths[target].relative_to(W)),sha256=H(paths[target]),frozen_manifest=str(manifest.relative_to(W)),manifest_sha256=H(manifest))],predecessor_sources_in_closure=52,fresh_N2_passed_sources=passed,bindings=bindings,API_rebase_findings=['The existing gluing source imports actual reciprocal normalization and the checked baseline GenericOpenPushout318. It uses only Closure, intoInfinity and its now-passed open-immersion instance from the reciprocal namespace; no repaired private tower or action telescope is a qualified caller.', 'The finite and reciprocal structure maps retain the identical actual normalized overlap domain. Both maps and native open-immersion instances now pass in the exact N2 context.', 'The model remains the literal Scheme pushout; chart maps are its coprojections. GenericOpenPushout318.square yields the intersection pullback. No finite global normalization, properness, normality, regularity or KS statement is added.', 'Split planned N3: only the one gluing source is selected. Independent reciprocal fraction-field source and its two inferred tower proofs are deferred to a separate checkpoint.'],source_modifications=[],local_lean_run=False,publication_authorized_by_this_manifest=False,independent_N2_runtime_authentication_pending=False,next_gate='Independent exact dependency/source rebase review, then separately authorized immutable integration and hosted target53 replay')
out=W/'geometry-n3a-gluing-rebase/REBASE.json';out.write_text(json.dumps(v,indent=2)+'\n');print('manifest',H(out),'bindings',len(bindings),'draft',len(order),'baseline',len(bo),'new',v['new_sources'])
