"""Read-only source-identity check against an already verified published commit.

This does not publish, compile Lean, or infer hosted proof success. A caller must
supply the actual remote-publication receipt separately before binding metadata.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
B=Path(__file__).resolve().parent;D=B/'experiments/original-regular-coordinate-injectivity-r1'
def h(b):return hashlib.sha256(b).hexdigest()
def verify(repo,commit):
 assert len(commit)==40 and all(c in '0123456789abcdef' for c in commit)
 actual=subprocess.check_output(['git','rev-parse',commit+'^{commit}'],cwd=repo,text=True).strip();assert actual==commit
 prefix='quartics/quartic-318-326/proof/experiments/pel-original-character-ordered-biholomorph-r17/'
 def published(name):return subprocess.check_output(['git','show',commit+':'+prefix+name],cwd=repo)
 intake=published('intake.json');app=published('APPLICATION.json')
 assert h(intake)==h((D/'UPSTREAM/intake.json').read_bytes()),'upstream intake differs'
 assert h(app)==h((D/'UPSTREAM/APPLICATION.json').read_bytes()),'upstream application differs'
 candidate=json.loads((D/'APPLICATION.json').read_text());new=candidate['new_sources'];inherited={n:sha for n,sha in candidate['sources'].items() if n not in new}
 for n,sha in inherited.items():assert h(published(n))==sha==h((D/n).read_bytes()),n
 i=json.loads((D/'intake.json').read_text());assert len(i['order'])==489 and len(new)==5 and len(inherited)==484
 scripts=repo/'scripts';sys.path.insert(0,str(scripts));import check_progress_experiment as ce
 plan=ce.ci.derive_plan();_,_,direct,_=ce.packet(D.name,plan,root=D.parent);base=ce.required_baseline(plan,direct)
 expected=json.loads((D/'PROVENANCE.json').read_text())['baseline_order'];assert base==expected and len(base)==73
 return {'check':'READ_ONLY_EXACT_PUBLISHED_SOURCE_IDENTITY','commit':commit,'upstream_packet':'pel-original-character-ordered-biholomorph-r17','upstream_intake_sha256':h(intake),'upstream_application_sha256':h(app),'inherited_sources_checked':len(inherited),'new_sources_unchanged':new,'experimental_roots':489,'accepted_baseline_dependencies':73,'intake_sha256':h((D/'intake.json').read_bytes()),'local_lean_run':False,'kernel_verified':False,'remote_publication_receipt_required_separately':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--commit',required=True);a=p.parse_args();print(json.dumps(verify(a.repo.resolve(),a.commit),indent=2))
