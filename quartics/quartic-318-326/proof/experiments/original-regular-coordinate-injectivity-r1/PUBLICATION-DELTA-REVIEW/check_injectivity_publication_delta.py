from pathlib import Path
import sys, json, hashlib, subprocess, shutil
sys.dont_write_bytecode=True
B=Path('/workspace/scratch/41c6d5925c0e'); O=B/'review43597228569'; R=B/'pel-integration43597228569/repo'; P=B/'picard-original-evaluation-experiment/experiments/original-regular-coordinate-injectivity-r1'; S=P/'PACKET-REVIEW/PRE-PUBLICATION-BIND'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((P/'APPLICATION.json').read_text()); old=json.loads((S/'APPLICATION.json').read_text()); before=json.loads((O/'ORIGINAL-INJECTIVITY-PACKET-CHECK.json').read_text()); pr=json.loads((P/'PROVENANCE.json').read_text()); oldpr=json.loads((S/'PROVENANCE.json').read_text())
assert sha(P/'APPLICATION.json')=='4119047e9205a512c8c2a20fea0fff05c4a3d036482cb8942319dca8c253f9e7'
for n,k in [('APPLICATION.json','application_sha256'),('README.md','readme_sha256'),('PROVENANCE.json','provenance_sha256')]:assert sha(S/n)==before[k]
changed={k for k in a.keys()|old.keys() if a.get(k)!=old.get(k)}
assert changed=={'current_packet_review_scope','known_remaining_risk','bindings','upstream_publication_verified','packet_review','current_packet_review_complete'}
assert a['sources']==before['source_sha256'] and a['obligations']==before['obligations'];assert sha(P/'intake.json')==before['intake_sha256']
for flag in ['local_lean_run','kernel_verified','independent_acceptance','full_arithmetic_theorem_proved']:assert a[flag] is False
assert a['upstream_publication_verified'] and a['current_packet_review_complete']
assert {k for k in pr.keys()|oldpr.keys() if pr.get(k)!=oldpr.get(k)}=={'initial_packaging_scope','scope','actual_publication'}
assert pr['initial_packaging_scope']==oldpr['scope']
for fn,h in a['bindings'].items():assert sha(P/fn)==h,fn
for fn,h in old['bindings'].items():assert a['bindings'][fn]==h or fn in ['README.md','PROVENANCE.json'],fn
for fn,h in a['sources'].items():assert sha(P/fn)==h,fn
receipt=json.loads((P/'UPSTREAM/PUBLICATION/UPSTREAM-GITHUB-PUBLICATION.json').read_text());commits=['60d4fd73ed84e5a3b274f711dc4d593090b63f58','57227e167abe49436d651b932ff75d5bdf9b5898'];assert receipt['proof_commit']['sha']==commits[0] and receipt['branch_lookup']['observed']['sha']==commits[1]
up='quartics/quartic-318-326/proof/experiments/pel-original-character-ordered-biholomorph-r17/'
for c in commits:
 for fn,h in a['sources'].items():
  if fn in a['new_sources']:continue
  v=subprocess.check_output(['git','show',c+':'+up+fn],cwd=R);assert hashlib.sha256(v).hexdigest()==h,(c,fn)
 for fn in ['intake.json','APPLICATION.json']:assert subprocess.check_output(['git','show',c+':'+up+fn],cwd=R)==(P/'UPSTREAM'/fn).read_bytes()
assert len(a['sources'])-len(a['new_sources'])==484
m=json.loads((O/'ORIGINAL-INJECTIVITY-PACKET-BINDINGS.json').read_text())
for ref,h in m['reviewer_evidence'].items():assert sha(O/ref)==h and sha(P/'PACKET-REVIEW'/ref)==h,ref
sys.path.insert(0,str(R/'scripts'));import check_progress_experiment as ce
ce.packet(P.name,ce.ci.derive_plan(),P.parent)
Q=O/'injectivity-publication-delta-snapshots';Q.mkdir(exist_ok=True)
for n in ['APPLICATION.json','README.md','PROVENANCE.json','intake.json']+[str(x.relative_to(P)) for x in (P/'UPSTREAM/PUBLICATION').rglob('*') if x.is_file()]:
 q=Q/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(P/n,q)
j={'status':'PASS_PUBLICATION_GATE_METADATA_DELTA_ONLY','application_sha256':sha(P/'APPLICATION.json'),'intake_sha256':sha(P/'intake.json'),'readme_sha256':sha(P/'README.md'),'provenance_sha256':sha(P/'PROVENANCE.json'),'changed_application_keys':sorted(changed),'all_sources_unchanged':489,'obligations_unchanged':9,'upstream_files_verified_at_each_commit':484,'commits':commits,'native_packet_check':'PASS','local_lean_run':False,'kernel_verified':False,'final_integrated_index_review_complete':False}
(O/'INJECTIVITY-PUBLICATION-DELTA-CHECK.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
