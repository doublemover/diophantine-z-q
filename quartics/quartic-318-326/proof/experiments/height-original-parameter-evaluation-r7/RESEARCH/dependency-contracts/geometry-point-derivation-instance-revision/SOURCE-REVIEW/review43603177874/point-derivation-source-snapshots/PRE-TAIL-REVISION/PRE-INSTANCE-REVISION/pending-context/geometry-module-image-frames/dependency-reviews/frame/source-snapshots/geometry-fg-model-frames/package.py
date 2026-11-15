from pathlib import Path
import json,hashlib,tarfile
r=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ob=[
('required_inputs','A specified finite-place embedded model M, finite generation, and a nonzero member.','M.FG and the actual a0 membership/nonvanishing, not a frame/rank/KS premise.','Theorem exists_generator extracts its finite-span witness and augments the set by a0.'),
('constructed_objects','An actual free integral frame of the same M.','Maximum-norm generator gamma, proof gamma≠0, equality lattice(gamma)=M and existing principal basis transported by that equality.','Both lattice inclusions are proved from exact norm membership and membership of gamma in M.'),
('index_and_domain_coverage','Every excluded finite place; no zero-model or zero-pair exception silently removed.','FiniteModels quantifies exactly BadPlace; each model contains nonzero original a0.','No frame exists for zero M, but actual a0 rules it out explicitly; no good/bad place is omitted.'),
('transition_maps','Same field embedding and original valuation integer action.','Native lattice/basis and LinearEquiv.ofEq, whose coercion preserves the field element.','frame_value records the actual coefficient formula; no alternate completion or rational frame introduced.'),
('scalars_and_signs','Actual finite norm normalization and every retained bad defect.','Existing bounded_iff/mem_iff_norm for the exact finite-place ring.','Largest-norm selection is only a basis choice for M; does not equate M with section span or force defect1; no scalar210 or Hodge normalization changed.'),
('consumer_identity','Previous ModelFrames interface consumed by the exact original metric-section bridge.','modelFrames.model is literally D.model; assembled_bad is the proved exact model equality.','The global Hodge/KS maps and metrics remain supplied downstream, not synthesized from this frame.'),
('exceptional_cases','Finite generation/nonzero prerequisites, arbitrary parameter c and all actual branch labels.','All original hn,i,c,t retained.','Finite generation is still a displayed geometric assumption; no claim arbitrary infinitely generated submodules are principal.'),
('downstream_and_history','Previous map and section-defect slices plus original published lattice chain.','Source-reviewed map slice reused unchanged; original pair and defects remain unchanged.','This is a new frame producer, not a proof of actual global bad model/coherence/Hodge realization or a historical gap claim.'),
('verification_boundary','Independent source review and reachable hosted whole-module validation.','Pinned native APIs, standalone sources/contract only.','No local Lean, active packet, resource change, admission, metric construction or proof acceptance.')]
a={'status':'SOURCE_CANDIDATE_REVIEW_PENDING','author':'geometry_repair_resume','production_changes':False,'global_realization_proved':False,'local_lean_run':False,'obligations':[{'id':i,'required_input':q,'constructed_input':c,'justification':j,'source_refs':['sources/FiniteGeneratedPlaceFrame318.lean','sources/OriginalFiniteModelFrames318.lean','primary/PROVENANCE.json'],'evidence':['README.md','primary/ActualFinitePlaceIntegers318.lean','primary/FinitePlacePrincipalLattice318.lean']} for i,q,c,j in ob],'bindings':{str(p.relative_to(r)):sha(p) for p in r.rglob('*') if p.is_file() and p.name not in ['APPLICATION.json','geometry-fg-model-frames.tar.gz','ARCHIVE-RECEIPT.json']}}
(r/'APPLICATION.json').write_text(json.dumps(a,indent=2)+'\n')
for p,h in a['bindings'].items():assert sha(r/p)==h
for f in (r/'sources').glob('*.lean'):
 s=f.read_text();assert all(x not in s for x in ['sorry','axiom ','set_option ','unsafe '])
o=r/'geometry-fg-model-frames.tar.gz';ps=sorted(p for p in r.rglob('*') if p.is_file() and p.name not in [o.name,'ARCHIVE-RECEIPT.json'])
with tarfile.open(o,'w:gz') as t:
 for p in ps:t.add(p,arcname=str(p.relative_to(r)))
with tarfile.open(o,'r:gz') as t:
 for p in ps:assert t.extractfile(str(p.relative_to(r))).read()==p.read_bytes()
d={'sha256':sha(o),'bytes':o.stat().st_size,'files':len(ps),'application_sha256':sha(r/'APPLICATION.json'),'status':a['status']};(r/'ARCHIVE-RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(d)
