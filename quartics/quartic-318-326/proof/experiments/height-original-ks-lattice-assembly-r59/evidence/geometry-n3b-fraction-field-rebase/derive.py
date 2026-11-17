from pathlib import Path
import hashlib,json,sys,subprocess
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'geometry-ks55-gluing-integration';P=R/'quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r55';B=R/'quartics/quartic-318-326/proof/progress'
sys.path.insert(0,str(R/'scripts'));from check_progress_lean import import_names
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source='df8eec3e75728d7502881be3e4f09d63978ebaaf';prefix='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r55'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
assert git('rev-parse',source+':'+prefix).decode().strip()=='194a611e8772e0991262ff909e93df0b5f0ecc66'
intake=json.loads((P/'intake.json').read_text());base=json.loads((B/'checkpoint-manifest.json').read_text());baseline=set(base['module_order']);paths={n:P/(n+'.lean') for n in intake['order']}
target='OriginalIntegerReciprocalFractionField318';paths[target]=W/'recovery-n3b-fraction-tower-carriers'/f'{target}.lean';manifest=W/'geometry-reciprocal-fraction-field/MANIFEST.json';correction=W/'recovery-n3b-fraction-tower-carriers/SOURCE-APPLICATION.json';assert H(paths[target])==json.loads(correction.read_text())['after_sha256']
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
host=W/'hosted-monitor-43979792804/gluing53';inv=json.loads((host/'INVENTORY.json').read_text());auth=W/'resume-independent-review/KS55-GLUING53-HOSTED-43979792804-ASTRA-REVIEW.json';av=json.loads(auth.read_text());assert set(order)-{target}<=set(inv['audit']['modules']);assert len(set(order)-{target})==52;passed={}
for n in order:
 if n==target:continue
 sha=H(paths[n]);assert sha==intake['files'][n+'.lean']['sha256'];assert hashlib.sha256(git('show',source+':'+prefix+'/'+n+'.lean')).hexdigest()==sha;passed[n]=sha
bindings={str(paths[n].relative_to(W)):H(paths[n]) for n in order}
for n in bo:q=B/(n.replace('.','/')+'.lean');bindings[str(q.relative_to(W))]=H(q)
for q in [manifest,P/'intake.json',B/'checkpoint-manifest.json',host/'INVENTORY.json',host/'BINDING-VERIFIED.json',auth,W/'resume-independent-review/RECIPROCAL-FRACTION-FIELD-ASTRA-REVIEW.json',correction]:bindings[str(q.relative_to(W))]=H(q)
v=dict(status='DEPENDENCY_REBASE_CANDIDATE_NOT_NEW_LEAN_ACCEPTANCE',passed_source_commit=source,passed_packet=P.name,passed_packet_subtree='194a611e8772e0991262ff909e93df0b5f0ecc66',target=target,draft_dependency_order=order,baseline_dependency_order=bo,draft_closure_count=len(order),baseline_closure_count=len(bo),new_sources=[dict(module=target,path=str(paths[target].relative_to(W)),sha256=H(paths[target]),frozen_manifest=str(manifest.relative_to(W)),manifest_sha256=H(manifest))],predecessor_sources_in_closure=52,fresh_passed_sources=passed,bindings=bindings,API_rebase_findings=['The selected source is a separately frozen two-site explicit-carrier proof revision of the existing reviewed reciprocal fraction-field source. Public tower goal types and all named map/action definitions are unchanged.', 'Finite overlap fraction field is derived before reciprocalBaseAlgebra and reciprocalLaurentAlgebra attributes are installed. The common Laurent action remains the accepted laurentAlgebra; reciprocal descent uses its own integral closure and accepted overlap localization.', 'The exact target closure is the 52 current N2 predecessors plus this one source; the already passed gluing source is preserved in the packet but not imported by this target.', 'This proves only same-original-field fraction-ring and integral-closedness statements if accepted. No reciprocal order comparison, finite normalization morphism, properness, regularity or KS layer is added.'],source_modifications=[dict(path=str(correction.relative_to(W)),sha256=H(correction),kind="Two explicit R/S/A local proof arguments; unchanged telescope/maps/actions")],local_lean_run=False,publication_authorized_by_this_manifest=False,independent_prior_runtime_authentication_pending=False,next_gate='Independent exact dependency/source rebase review, then separately authorized immutable integration and hosted target53 replay')
out=W/'geometry-n3b-fraction-field-rebase/REBASE.json';out.write_text(json.dumps(v,indent=2)+'\n');print('manifest',H(out),'bindings',len(bindings),'draft',len(order),'baseline',len(bo),'new',v['new_sources'])
