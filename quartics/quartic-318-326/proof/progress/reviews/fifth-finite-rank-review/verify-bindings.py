from pathlib import Path
import hashlib,json,re
B=Path('/workspace/scratch/2cb21e4e0864');P=B/'recovery-hodge-0358/fifth-finite-rank-review';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();checks=[];pins={}
def ck(path,expected,kind):
 p=B/path;actual=H(p);assert actual==expected,(path,expected,actual);checks.append(dict(path=path,expected=expected,actual=actual,kind=kind));pins[path]=actual
pkts={'recovery-geometric-0358/fifth-generic-degree':'ec18267120d1b5c0c88941c0e967ef354ab6f302f65f03e0e0d8884287ece36d','recovery-geometric-0358/fifth-finite-flat-rank':'74067168e9e11b9286f9453f1f38e8500b8cad90ed4f1b228e60cbe6e70a9cc0'}
for root,h in pkts.items():
 ck(root+'/receipt.json',h,'assigned receipt')
 r=json.loads((B/root/'receipt.json').read_text())
 for f,h in r['artifacts'].items():ck(root+'/'+f,h,'target artifact')
 for f,h in r['dependency_receipts'].items():ck(f,h,'retained predecessor receipt')
 d=json.loads((B/root/'DEPENDENCIES.json').read_text())
 for f,h in d.items():ck(f,h,'dependency manifest')
ck('recovery-contact-0358/fifth-global-source-independent-review/acceptance.json','87aa247f2261ae57ec6619e7a2944b1e3ede774b4de2d8aa9cc520d99f234594','separate predecessor consuming review')
reads=['recovery-contact-0358/completed-character-function-field/ActualOpenFractionField318.lean','recovery-contact-0358/completed-character-pullback-degree/DominantFunctionField318.lean','recovery-contact-0358/completed-character-pullback-degree/AffineFunctionFieldMap318.lean','recovery-contact-0358/completed-character-pullback-degree/OpenFunctionFieldSquare318.lean','diophantine-z-q/quartics/quartic-318-326/proof/progress/OpenFunctionField318.lean','fifth-source-infinity/FifthSourceInfinityCoordinates318.lean','fifth-target-parameter/FifthTargetParameter318.lean','fifth-target-parameter/FifthTargetParameterRestriction318.lean','recovery-geometric-0358/finite-chart-density/SchematicEqualityExtension318.lean','recovery-contact-0358/completed-character-finite/ProperFiniteFiberDescent318.lean','recovery-contact-0358/completed-character-flat/CompletedRationalDedekind318.lean','recovery-contact-0358/completed-character-flat/DedekindAffineFlat318.lean','recovery-modular-0358/finite-flat-generic-rank/FiniteFlatGenericRank318.lean','recovery-geometric-0358/fifth-character-field-order/FifthCharacterField318.lean','recovery-geometric-0358/fifth-global-source-map/FifthCompletedGlobal318.lean','fifth-character-short-model/FifthCharacterShortPolynomial318.lean']
for path in reads:pins[path]=H(B/path)
for root,log,marker in [('recovery-geometric-0358/fifth-generic-degree','generic-degree-audit.log','FIFTH_GENERIC_DEGREE_AUDIT_PASS declarations=65 modules=3'),('recovery-geometric-0358/fifth-finite-flat-rank','finite-flat-rank-audit.log','FIFTH_FINITE_FLAT_RANK_AUDIT_PASS declarations=21 modules=4')]:assert marker in (B/root/log).read_text()
for root,logs in [('recovery-geometric-0358/fifth-generic-degree',['degree-check1.log','degree-check2.log']),('recovery-geometric-0358/fifth-finite-flat-rank',['finite-check3.log','finite-check4.log'])]:
 for log in logs:
  s=(B/root/log).read_text();assert 'ACQUIRED' in s and 'RELEASED' in s and 'error:' not in s
out=dict(status='ALL_BINDINGS_MATCH',checks=checks,hash_comparisons=len(checks),unique_files=len(pins),source_reads=reads,all_pins=pins,validation='Read-only SHA256 verification and retained log inspection. No Lean or dependency replay.')
(P/'BINDINGS.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(checks),'comparisons',len(pins),'files')
