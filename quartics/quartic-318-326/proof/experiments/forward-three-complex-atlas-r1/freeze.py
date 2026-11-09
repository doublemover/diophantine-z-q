from pathlib import Path
import hashlib,json,re,sys,datetime,subprocess
root=Path('/workspace/scratch/2cb21e4e0864/quartic-proof');b=root/'quartics/quartic-318-326/proof/progress';p=b.parent/'experiments/forward-three-complex-atlas-r1';lib=Path('/workspace/shared/analytic-complex-atlas-r1/final-lib')
sys.path.insert(0,str(root/'scripts'));from check_progress_lean import import_names;from check_lean import code_only
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();write=lambda f,d:(p/f).write_text(json.dumps(d,indent=2)+'\n')
mods=json.loads(Path('/workspace/shared/analytic-complex-atlas-r1/order.json').read_text());sources={n+'.lean':sha(p/(n+'.lean')) for n in mods};imports={n:sorted(import_names((p/(n+'.lean')).read_text())) for n in mods}
for n in mods:assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|constant)\b',code_only((p/(n+'.lean')).read_text()))
auditmatch=re.search(r'EXPERIMENT_AUDIT_PASS declarations=(\d+) modules=37',(p/'checks/ExperimentAudit.log').read_text());assert auditmatch
count=int(auditmatch[1]);pins={};direct=set();up=set()
def visit(n):
 if n in mods or n in pins:return
 f=b/(n+'.lean')
 if not f.is_file():return
 pins[n]=sha(f)
 for d in import_names(f.read_text()):visit(d)
for n in mods:
 for d in imports[n]:
  if d not in mods:
   if (b/(d+'.lean')).is_file():direct.add(d);visit(d)
   else:up.add(d)
for n,h in pins.items():assert hashlib.sha256(subprocess.check_output(['git','show','5e483a2:quartics/quartic-318-326/proof/progress/'+n+'.lean'],cwd=root)).hexdigest()==h
for prev in ['forward-three-holomorphic-descent-r1']:
 for n in json.loads((p.parent/prev/'intake.json').read_text())['order']:assert sha(p/(n+'.lean'))==sha(p.parent/prev/(n+'.lean'))
write('baseline-source-pins.json',dict(sorted(pins.items())))
mathlib=b/'.lake/packages/mathlib'
primary_paths=[
'Mathlib/Analysis/Analytic/IsolatedZeros.lean',
'Mathlib/Analysis/Analytic/ChangeOrigin.lean',
'Mathlib/Analysis/Analytic/Composition.lean',
'Mathlib/Analysis/Calculus/MeanValue.lean',
'Mathlib/Analysis/Calculus/FDeriv/Analytic.lean',
'Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean',
'Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean',
'Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean',
'Mathlib/Analysis/Complex/OpenMapping.lean',
'Mathlib/Analysis/Complex/RemovableSingularity.lean',
'Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean',
'Mathlib/Analysis/Meromorphic/Order.lean',
'Mathlib/Topology/OpenPartialHomeomorph/Continuity.lean',
'Mathlib/Topology/Compactification/OnePoint/Basic.lean',
'Mathlib/Topology/Algebra/GroupWithZero.lean',
'Mathlib/Analysis/Normed/Field/Lemmas.lean',
'Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean',
'Mathlib/Geometry/Manifold/IsManifold/Basic.lean',
'Mathlib/Geometry/Manifold/ContMDiff/Defs.lean',
'Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean',
'Mathlib/Geometry/Manifold/Diffeomorph.lean']
primary={name:sha(mathlib/name) for name in primary_paths}
for name,h in primary.items():
 assert hashlib.sha256(subprocess.check_output(['git','show','56a005855ea17e0b0958f73ec801ae140b0a1679:'+name],cwd=mathlib)).hexdigest()==h
write('primary-source-pins.json',dict(mathlib_commit='56a005855ea17e0b0958f73ec801ae140b0a1679',sources=primary))

s=(p/'README.md').read_text().replace('Status: final strict replay and distinct non-author review pending.','Status: frozen. Thirty-seven sources passed fresh strict replay and a private-inclusive\nrecursive audit of '+str(count)+' declarations. Distinct non-author review is pending.');(p/'README.md').write_text(s)
paras=re.findall(r'(?ms)^(\d)\. (.*?)(?=^\d\. |^## Remaining)',s[s.index('## Exact application contract'):]);assert len(paras)==9
meta=[
('Independent ordinary complex sphere topology and inversion.','Existing OnePoint topology, literal inversion, zero/infinity continuity and involution.','SphereInversion318.lean'),
('Every target point in a genuine coordinate chart.','Independent finite and reciprocal charts, full coordinate targets, selected chart membership.','SphereCharts318.lean'),
('Analytic coordinate transitions on exact overlaps.','Both overlaps are exactly C* and both maps literal reciprocal, giving IsManifold.','SphereComplexCurve318.lean'),
('Actual original compact filling and transitions.','Unchanged Filled topology, exact compactHomeomorph, pulled chart transitions and compact complex manifold.','ActualThreeComplexAtlas318.lean'),
('Exact bundled analytic scalar germ criterion.','ContMDiffAt analytic regularity equals the exact chosen target expression germ.','ActualThreeCanonicalAnalytic318.lean'),
('Canonical original quotient holomorphy, including elliptic points.','Bundled source germs equal independent all-representative orbit-pullback holomorphy.','ActualThreeCanonicalAnalytic318.lean'),
('Every actual original q-disc germ at the added cusps.','Actual end exhaustion and exact finite/reciprocal target expressions identify the bundled cusp criterion.','ActualThreeCanonicalAnalytic318.lean'),
('Exact global analytic equivalence and inverse.','Original compact map and inverse are complex analytic in the proven canonical structure.','ActualThreeBiholomorph318.lean'),
('New strict replay and distinct review of the changed route.','Thirty-seven freshly replayed sources, thirty-one unchanged predecessors; arithmetic and PEL realization remain excluded.','receipt.json')]



ob=[]
for (i,para),(required,constructed,ref) in zip(paras,meta):
 title,rest=para.split('.',1);ob.append(dict(name=title,required_input=required,constructed_input=constructed,justification=' '.join(rest.split()),sources=[ref,'README.md']))
write('APPLICATION.json',dict(producer='/root/advance_analytic_geometry',claim='The unchanged original compact level-three filling carries a genuine complex analytic manifold structure whose scalar germs equal the original orbit-pullback and actual q-disc germs, and its unchanged compact T comparison is a biholomorphism with the independently charted standard complex sphere.',sources=sources,readme_sha256=sha(p/'README.md'),obligations=ob))
write('intake.json',dict(packet=p.name,status=f'STRICT_LOCAL_PASS_RECURSIVE_AUDIT_{count}_DECLARATIONS_PENDING_NONAUTHOR_REVIEW',order=mods,files={n+'.lean':dict(sha256=sources[n+'.lean'],imports=imports[n]) for n in mods},scope='Actual compact complex analytic manifold, canonical original quotient/cusp germ identification and original compact biholomorphism. No arithmetic scheme analytification or PEL realization.'))
write('receipt.json',dict(status='PASS',producer='/root/advance_analytic_geometry',checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lean_version='4.35.0',mathlib_commit='56a005855ea17e0b0958f73ec801ae140b0a1679',flags=['-j1','-M6144','-Ddebug.skipKernelTC=false'],source_order=mods,sources=sources,audit_declarations=count,audit_modules=37,allowed_axioms=['propext','Classical.choice','Quot.sound'],baseline_source_closure_count=len(pins),baseline_source_pins_sha256=sha(p/'baseline-source-pins.json'),primary_source_pins_sha256=sha(p/'primary-source-pins.json'),primary_source_count=len(primary),direct_baseline_imports=sorted(direct),upstream_imports=sorted(up),application_sha256=sha(p/'APPLICATION.json'),intake_sha256=sha(p/'intake.json'),readme_sha256=sha(p/'README.md'),audit_source_sha256=sha(p/'ExperimentAudit.lean'),logs={f.name:sha(f) for f in sorted((p/'checks').glob('*.log'))},objects={n:sha(lib/(n+'.olean')) for n in mods},predecessor_packets={name:{f:sha(p.parent/name/f) for f in ['receipt.json','APPLICATION.json','intake.json','README.md']} for name in ['forward-three-holomorphic-descent-r1']},independent_review='PENDING',baseline_promotion=False,full_arithmetic_theorem_proved=False,verification_scope='Fresh serial strict thirty-seven-source replay; recursive all-private audit. Exact original baseline source pins reused, no clean upstream rebuild claimed.'))
(p/'SHA256SUMS').write_text(''.join(sha(f)+'  '+str(f.relative_to(p))+'\n' for f in sorted(p.rglob('*')) if f.is_file() and f.name!='SHA256SUMS'))
print(json.dumps(dict(status='FROZEN',sources=sources,receipt_sha256=sha(p/'receipt.json'),application_sha256=sha(p/'APPLICATION.json'),intake_sha256=sha(p/'intake.json'),audit=count,baseline=len(pins)),indent=2))
