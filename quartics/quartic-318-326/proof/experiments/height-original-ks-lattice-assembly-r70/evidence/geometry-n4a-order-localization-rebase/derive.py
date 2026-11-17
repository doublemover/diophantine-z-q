from pathlib import Path
import hashlib,json,sys,subprocess
W=Path('/workspace/scratch/41c6d5925c0e');R=W/'geometry-ks56-fraction-field-integration';P=R/'quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r56';B=R/'quartics/quartic-318-326/proof/progress'
sys.path.insert(0,str(R/'scripts'));from check_progress_lean import import_names
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source='30c51878054f3cd701dc15e99d4dfe1118fabe44';prefix='quartics/quartic-318-326/proof/experiments/height-original-ks-lattice-assembly-r56'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
assert git('rev-parse',source+':'+prefix).decode().strip()=='adb5e6654d25bf55951d6f7e607d49e9eff351c2'
intake=json.loads((P/'intake.json').read_text());base=json.loads((B/'checkpoint-manifest.json').read_text());baseline=set(base['module_order']);paths={n:P/(n+'.lean') for n in intake['order']}
target='FourRootOrderLocalizationMaps318';paths[target]=W/'geometry-reciprocal-order-map/sources'/f'{target}.lean';manifest=W/'geometry-reciprocal-order-map/MANIFEST.json';assert H(paths[target])==json.loads(manifest.read_text())['sources'][target+'.lean']
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
walk(target);assert len(order)==40
host=W/'hosted-monitor-43986190361/fraction53';inv=json.loads((host/'INVENTORY.json').read_text());auth=W/'resume-independent-review/KS56-FRACTION53-HOSTED-43986190361-ASTRA-REVIEW.json';av=json.loads(auth.read_text());assert set(order)-{target} <= set(inv['audit']['modules']);passed={}
for n in order:
 if n==target:continue
 sha=H(paths[n]);assert sha==intake['files'][n+'.lean']['sha256'];assert hashlib.sha256(git('show',source+':'+prefix+'/'+n+'.lean')).hexdigest()==sha;passed[n]=sha
bindings={str(paths[n].relative_to(W)):H(paths[n]) for n in order}
for n in bo:q=B/(n.replace('.','/')+'.lean');bindings[str(q.relative_to(W))]=H(q)
for q in [manifest,P/'intake.json',B/'checkpoint-manifest.json',host/'INVENTORY.json',host/'BINDING-VERIFIED.json',auth,W/'resume-independent-review/RECIPROCAL-ORDER-NORMALIZATION-ASTRA-REVIEW.json']:bindings[str(q.relative_to(W))]=H(q)
v=dict(status='DEPENDENCY_REBASE_CANDIDATE_NOT_NEW_LEAN_ACCEPTANCE',passed_source_commit=source,passed_packet=P.name,passed_packet_subtree='adb5e6654d25bf55951d6f7e607d49e9eff351c2',target=target,draft_dependency_order=order,baseline_dependency_order=bo,draft_closure_count=len(order),baseline_closure_count=len(bo),new_sources=[dict(module=target,path=str(paths[target].relative_to(W)),sha256=H(paths[target]),frozen_manifest=str(manifest.relative_to(W)),manifest_sha256=H(manifest))],predecessor_sources_in_closure=39,fresh_passed_sources=passed,bindings=bindings,API_rebase_findings=['Only the existing generic FourRootOrderLocalizationMaps318 source is selected. Its sole project import FourRootOrderOpenMaps318 is unchanged and belongs to the exact current passed closure.', 'The generic sourceAlgebra is the actual base-change RingHom followed by the supplied equivalence. Its source-order linear localizedEquiv and localization theorem retain those exact maps; no alternate or abstract field embedding is substituted.', 'Injectivity is derived from localization and torsion-free finite-free source-order structure over a domain coefficient ring. No source-order domain or irreducibility premise is assumed.', 'Split planned N4 into its earliest single generic helper, without OriginalIntegerCommonField318 or OriginalIntegerReciprocalOrderNormalization318. Existing gluing and fraction-field sources remain untouched in the predecessor packet. Tensor dictionary and localization transport elaboration remain hosted obligations.'],source_modifications=[],local_lean_run=False,publication_authorized_by_this_manifest=False,independent_prior_runtime_authentication_pending=False,next_gate='Independent exact dependency/source rebase review, then separately authorized immutable integration and hosted target40 replay')
out=W/'geometry-n4a-order-localization-rebase/REBASE.json';out.write_text(json.dumps(v,indent=2)+'\n');print('manifest',H(out),'bindings',len(bindings),'draft',len(order),'baseline',len(bo),'new',v['new_sources'])
