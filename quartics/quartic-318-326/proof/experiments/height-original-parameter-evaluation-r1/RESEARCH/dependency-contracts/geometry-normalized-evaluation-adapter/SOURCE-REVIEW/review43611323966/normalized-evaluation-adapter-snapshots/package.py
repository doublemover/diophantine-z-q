from pathlib import Path
import json,hashlib,shutil,subprocess,re,tarfile
r=Path(__file__).resolve().parent;root=r.parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();repo=root/'pel-integration43597228569/repo';head='57227e167abe49436d651b932ff75d5bdf9b5898'
contexts=['geometry-normalized-cotangent-inputs','geometry-point-derivation-instance-revision'];deps={}
for name in contexts:
 src=root/name;a=json.loads((src/'APPLICATION.json').read_text());dest=r/'dependency-snapshots'/name;assert not dest.exists();dest.mkdir(parents=True)
 for n in ['APPLICATION.json',*a['bindings']]:
  q=src/n;out=dest/n;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,out)
 for n,h in a['bindings'].items():assert H(dest/n)==h,n
 deps[name]={'application_sha256':H(src/'APPLICATION.json'),'status':a['status'],'sources':a['sources']}
closure=json.loads((root/'geometry-point-derivation-instance-revision/FUTURE-CLOSURE.json').read_text());old=closure['unchanged_predecessor_sources'];baseorder=closure['proposed_order'][:96]
pre='quartics/quartic-318-326/proof/experiments/height-normalized-valuative-center-r68/'
for n,h in old.items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',head+':'+pre+n])).hexdigest()==h
order=baseorder+['NormalizedChartFiniteType318','NormalizedIntegralPointInput318']+closure['proposed_order'][96:]+['NormalizedPointEvaluationInput318','NormalizedAllPlaceEvaluations318'];assert len(order)==len(set(order))==104
new={p.name:H(p) for p in sorted((r/'sources').glob('*.lean'))};assert len(new)==2
seen=set(order[:-2])
for n in order[-2:]:
 text=(r/'sources'/(n+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option',text)
 for d in re.findall(r'^public import ([\w.]+)',text,re.M):assert d in seen
 seen.add(n)
c={'active':False,'head':head,'predecessor_packet':'height-normalized-valuative-center-r68','unchanged_predecessor_sources':old,'dependencies':deps,'new_sources':new,'proposed_order':order};(r/'FUTURE-CLOSURE.json').write_text(json.dumps(c,indent=2)+'\n')
obs=[
('original_inputs','Original signed root equations with unit twists and nonzero radicands over a characteristic-zero fraction field of a DVR.','Nonzero y is proved, and the same all-place chart-center producer supplies integral point data.','No root nonvanishing, polynomial field identity or functional premise is added separately.'),
('objects','Same whole finite/reciprocal four-root order and actual V tensor_A Omega(A/V).','Adapter instantiates the exact constructed first-order functional at its original point f.','No field-differential replacement or alternative quotient model.'),
('domain','Every four-root label and every polynomial, all DVR residue characteristics with explicit original nonzero-radicand restriction.','Projection/input identities are whole-domain; finite and reciprocal cases both retained.','Zero-root/branch points are excluded explicitly only from this route; old all-point center is unchanged.'),
('maps','Literal A to V to K and all-place point f.','Full field-polynomial identity derives from integral identity and coordinate embedding.','No new action or reselected point, same units/parities/rescaling witnesses.'),
('scalars','u/e/s coefficient normalization, finite s_i times root and reciprocal s_i*t times root.','Nonzero-root proofs use these exact equations and finite/infinity functional definitions.','No canceled integral-unit premise; finite DT=1 and reciprocal Dw=1, not Dt.'),
('consumer','Actual finite cotangent evaluation image / FG / frame route.','ev exists with actual coordinate differential mapped to 1, hence supplies a nonzero image element.','Original section lifts and exact rational frame comparison remain missing; no maximal lattice equality.'),
('exceptional_cases','Nonunit twists, residue characteristic two, singular/torsion naive cotangent modules.','Only K inverses in pending first-order source; adapter introduces no inverses.','No regularity/source rank/injectivity or good-prime restriction.'),
('residual_geometry','Original dualizing/maximal model, Hodge determinant, native KS lower-image and metrics.','No changes to those interfaces or historical accepted sources.','No native KS map/model construction, finite support or height bound inferred.'),
('verification','Independent two-source plus pending dependency source review before any hosted packet.','Exact frozen dependency snapshots,104-module inactive closure,static no-admission and audit checks.','No local Lean, resources/cache/trust changes or full theorem acceptance.')]
a={'author':'geometry_repair_resume','status':'SOURCE_REVIEW_PENDING_NOT_ACTIVE','local_lean_run':False,'kernel_verified':False,'dependencies':deps,'sources':new,'all_place_nonzero_radicand_adapter_constructed':True,'original_quadratic_section_lifts_constructed':False,'native_KS_model_constructed':False,'obligations':[{'id':i,'required_input':q,'constructed_input':v,'justification':j,'source_refs':['README.md',*['sources/'+n for n in new]],'evidence':['FUTURE-CLOSURE.json']} for i,q,v,j in obs]}
cp=subprocess.run(['python','-B',str(repo/'scripts/check_audit_history.py'),'--self-test'],capture_output=True,text=True);(r/'audit-self-test.log').write_text(cp.stdout+cp.stderr);assert cp.returncode==0
out=r/'geometry-normalized-evaluation-adapter.tar.gz';exclude={'APPLICATION.json',out.name,'ARCHIVE-RECEIPT.json'};a['bindings']={str(p.relative_to(r)):H(p) for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in exclude};(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
files=[p for p in sorted(r.rglob('*')) if p.is_file() and p.name not in [out.name,'ARCHIVE-RECEIPT.json']]
with tarfile.open(out,'w:gz') as t:
 for p in files:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(out,'r:gz') as t:
 for p in files:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':H(out),'bytes':out.stat().st_size,'files':len(files),'application_sha256':H(r/'APPLICATION.json'),'sources':new,'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
