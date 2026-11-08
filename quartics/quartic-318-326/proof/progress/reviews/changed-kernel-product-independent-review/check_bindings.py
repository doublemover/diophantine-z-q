from pathlib import Path
import hashlib,json,re
root=Path('/workspace/scratch/2cb21e4e0864')
target=root/'recovery-geometric-0358/changed-kernel-product'
out=root/'recovery-modular-0358/changed-kernel-product-independent-review'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((target/'receipt.json').read_text())
expected='86e687d97c94c1d685fac64624096f74ef426cb2931b42e202e7d5902f7cc499'
checks=[{'path':str((target/'receipt.json').relative_to(root)),'expected':expected,'actual':sha(target/'receipt.json')}]
for name,digest in receipt['sha256'].items():
 p=target/name; checks.append({'path':str(p.relative_to(root)),'expected':digest,'actual':sha(p)})
for name,digest in receipt['dependency_receipts'].items():
 p=root/'recovery-geometric-0358'/name/'receipt.json'
 checks.append({'path':str(p.relative_to(root)),'expected':digest,'actual':sha(p)})
assert all(x['expected']==x['actual'] for x in checks)
log=(target/'bounded-audit.log').read_text()
entries=re.findall(r'^AXIOM_CHECK ([^:]+): \[([^\]]*)\]$',log,re.M)
assert len(entries)==175
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(a.strip() for a in axs.split(',') if a.strip())<=allowed for _,axs in entries)
assert all(any(name==endpoint for name,_ in entries) for endpoint in receipt['endpoints'])
assert 'CHANGED_FULL_KERNEL_AUDIT_PASS declarations=175 modules=4' in log
refs=[
'recovery-geometric-0358/kernel-base-change/ZeroFiberBaseChange318.lean',
'recovery-geometric-0358/kernel-base-change/CompletedKernelBaseChange318.lean',
'recovery-geometric-0358/kernel-base-change/ActualKernelBaseChange318.lean',
'recovery-geometric-0358/kernel-base-change/KernelScalarExtension318.lean',
'recovery-geometric-0358/literal-kernel-finite-etale/LiteralKernelCoordinateRing318.lean',
'recovery-geometric-0358/three-torsion-base-change/ThreeTorsionBaseChange318.lean',
'recovery-geometric-0358/three-torsion-base-change/ThreeTorsionSchemeBaseChange318.lean',
'recovery-geometric-0358/changed-primitive-kernel/ChangedPrimitiveKernel318.lean',
'recovery-geometric-0358/changed-primitive-kernel/CanonicalChangedPrimitive318.lean',
'completed-coefficient-base-change/CompletedAdditionCoefficient318.lean',
'kernel-base-change-independent-review/acceptance.json',
'kernel-finite-etale-independent-review/acceptance.json',
'recovery-modular-0358/primitive-base-change-independent-review/acceptance.json',
'recovery-modular-0358/changed-primitive-independent-review/acceptance.json',
'diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Pi.lean',
'diophantine-z-q/quartics/quartic-318-326/proof/progress/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean']
result={'status':'BINDINGS_AND_RETAINED_AUDIT_CHECK_PASS_NOT_FRESH_LEAN_REPLAY','checks':checks,'hash_comparisons':len(checks),'retained_audit_declarations':len(entries),'all_claimed_endpoints_present':True,'allowed_axioms':sorted(allowed),'additional_read_interfaces':{r:sha(root/r) for r in refs},'no_replay':True}
(out/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'hash_comparisons':len(checks),'audit_declarations':len(entries),'endpoints':len(receipt['endpoints']),'checks_sha256':sha(out/'checks.json')}))
