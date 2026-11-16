from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent
P=R/'successors/height-normalized-valuative-center-r69'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={'HOSTED_REPAIR.json':('33cd1d898ed31393b6909f9640ecd00636355d692e2013f0dfecca2fb7308efa','7a2aa4a44a64149396d2a3884b2334cdf6447d796c66b14d523d6c6615696a2e'),'SOURCE_VALIDATION.json':('96a5fff8f468d6672ed945470bea9f9b0c8c2e173b60a7fa99c445f33ffb02cd','cf78555cd58235252197ecc247657c62d22968731d19c21f628166673cb4c8ac')}
assert H(P/'APPLICATION.json')=='da1f9308bfe51c04aea91d437bd089582ee08755ad7ca17eea5b2a0914031c04'
a=json.loads((P/'PROPAGATION-REVIEWED-APPLICATION.json').read_text())
out=P/'RECONSTRUCTED-REVIEWED-EVIDENCE';assert not out.exists();out.mkdir()
# Preserve exact current bytes before deriving historical byte-equivalent snapshots.
for n in ['APPLICATION.json','HOSTED_REPAIR.json','SOURCE_VALIDATION.json']:
 shutil.copy2(P/n,out/('CURRENT-INPUT-'+n))
for n in ['build_successor.py','finalize_center.py','reconstruct_reviewed_receipts.py']:shutil.copy2(R/n,out/n)
rows={}
for n,(current,old) in expected.items():
 assert H(P/n)==current and a['bindings'][n]==old
 d=json.loads((P/n).read_text());assert d['propagation_review']=='PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING'
 d['propagation_review']='PENDING'
 b=(json.dumps(d,indent=2)+'\n').encode();assert hashlib.sha256(b).hexdigest()==old
 q=out/('RECONSTRUCTED-REVIEWED-'+n);q.write_bytes(b)
 # Invert only the one known value to verify exact current bytes.
 d['propagation_review']='PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING'
 assert (json.dumps(d,indent=2)+'\n').encode()==(P/n).read_bytes()
 rows[n]={'current_input_sha256':current,'historically_reviewed_sha256':old,'reconstructed_sha256':H(q),'reconstructed_path':q.name,'only_changed_key':'propagation_review','reviewed_value':'PENDING','current_value':'PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING','byte_exact_roundtrip':True}
account='''# Explicit hash-verified reconstruction, not retained originals\n\nThe exact reviewed HOSTED_REPAIR.json and SOURCE_VALIDATION.json byte sequences were not located in the final owner tree, local reviewed snapshots, current geometry archive, or inspected PEL recovery archives. Library read with version_id 0 returned the current version-1 content identifier/size; a version-scoped search yielded no historical file. No Library version was restored or mutated. These observations do not prove historical storage lacks the old bytes.\n\nThe original builder records propagation_review as PENDING. The finalizer replaced that existing value with PASS_SOURCE_AND_CONTRACT_ONLY_HOSTED_PENDING; it did not add a previously absent key. The included script copies and pins the unchanged current receipts, then reverses only that value using the original JSON indent-2/newline serialization. Each resulting SHA256 must equal the independent, pre-existing reviewed APPLICATION binding. Reapplying the status value must reproduce the current input bytes exactly.\n\nRECONSTRUCTED-REVIEWED-* files are explicitly reconstructed byte-equivalent snapshots, not retrieved/retained originals. Current source, intake, README, HOSTED_REPAIR.json and SOURCE_VALIDATION.json are unchanged. No claim of Lean or kernel acceptance changes. Independent narrow metadata addendum is required before refreeze.\n'''
(out/'RECONSTRUCTION-PROVENANCE.md').write_text(account)
manifest={'status':'HASH_EXACT_RECONSTRUCTION_PENDING_INDEPENDENT_ADDENDUM','method':'Reverse only existing propagation_review status value; verify pre-existing reviewed hashes and exact forward roundtrip','historical_storage_retrieved':False,'library_history_mutated':False,'local_lean_run':False,'current_application_sha256':H(P/'APPLICATION.json'),'reviewed_application_sha256':H(P/'PROPAGATION-REVIEWED-APPLICATION.json'),'receipts':rows,'evidence':{str(q.relative_to(out)):H(q) for q in sorted(out.rglob('*')) if q.is_file()}}
(out/'RECONSTRUCTION.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert H(P/'APPLICATION.json')==manifest['current_application_sha256']
for n,(current,old) in expected.items():assert H(P/n)==current
print(json.dumps(manifest,indent=2))
