from pathlib import Path
import json,hashlib
P=Path('/workspace/scratch/41c6d5925c0e/review43592150561');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
texts={
'PEL':'''# PEL five-packet propagation review

Verdict: PASS for exact-source propagation, current application contracts and evidence bindings only. No local Lean/Lake, candidate kernel acceptance or full packet/audit pass.

The frozen zero-r43, cotangent-r49, torsion-r23, character-r16 and trace-r16 APPLICATION identities are recorded in the manifest and immutable snapshots. Their 580/660/735/1169/1504 roots retain complete predecessor order and coverage. Exactly 11 copies of the three source-reviewed modules change: Hausdorff qualification four times, Coercivity three times, PrimeRightLattice four times. All 4637 other root occurrences are byte-identical, including every geometry source. Entire predecessor Git folders are identical at authentic observed 75be14ed and current integration base 2b151fc6.

All 45 structured obligations were reviewed, scoped to only the modules actually changed in each packet. Hausdorff keeps the original glued topology, eight infinity centers, finite/finite and mixed/infinity cases, and actual whole-curve T2 consumer. PrimeRightLattice keeps the full four-prime/two-row domain, arbitrary signed integer vectors, ordered quaternion product, residueHom, actual coordinates/rightMultiply and kernel-range consumer. No sampled generators, replacement lattice or smaller domain is substituted.

Coercivity is explicitly conditional on hτ:0<τ.im. Three public telescopes genuinely change by restoring that intended binder, in the existing consumer argument order. Theta and scaled-theta applications already supply τ,hτ; nonzero τ, norm-square positivity and the exact min-bound sum remain derived. The proof does not assume an independent positive constant or desired lower bound. All original real two-vectors, coefficients/signs and exact Gaussian energy remain. The machine telescope flag is true exactly in the three packets that receive Coercivity. No blanket literal-statement preservation is asserted for this change.

Trace candidly preserves the earlier same-public-API RootGenerators proof-body variance. Its ordinary hosted run stopped in PrimeRightLattice, did not reach geometry, and cannot inherit a center-only GlobalComparison pass as a trace pass. The known full-module CommonRestriction failure and separately retained earlier geometry evidence remain disclosed. No new geometry repair or preventive edit is included.

Independent native packet/import/hash/schema/binding checks PASS for all five, and all 32 present classification aliases reject false-module mutations. Every declared binding and every exact authored source-review companion is verified. Each own RESULT binds its actual predecessor intake; peer evidence is not substituted for own lane provenance. README descriptions, native primary and actual consumer references resolve. Resources/trust settings and false acceptance flags are unchanged. The initial companion checker schema-assumption failure and corrected v2 PASS are retained, with no owner changes.

Only metadata-only final review attachment is cleared after preserving each exact reviewed raw APP. No source, intake, README or obligation text change is covered. Final integrated index and hosted checking remain separate.
''',
'PICARD':'''# Picard two-packet propagation review

Verdict: PASS for current nine-obligation contracts, exact-source propagation and provenance only. No local Lean, candidate kernel acceptance or complete packet/audit pass.

Gluing-r15 retains all 1298 roots/order; only OriginalLineSquareSections318 changes to reviewed d0493006. Five-r19 retains all 213 roots/order; only OriginalDualAlgebraNormTrace318 changes to reviewed beb08f2c. All 1509 other root occurrences are identical. The frozen APP hashes are 8beecbfc5e4ba24c2ca745979136b6b072dd9f70ec5778dee15c42eb941f39c9 and 4dddb5503d6b55759aca695888af5e146c68cd55629c07d4d1219086b24804b2. Entire predecessor folders are identical at authentic observed 75be14ed and integration base 2b151fc6.

All 18 newly authored obligations were reviewed. The gluing repair retains arbitrary schemes/module objects and every whole section, all h/h′/ha/hb/he path equations, original pullback objects and exact comparison arrows. Identity-left cancellation and explicit naturality equalities have the original reversed first and forward last orientations beneath unchanged outer maps. Both finite/infinity restriction squares and their Cech finite_square/infinity_square consumers remain literal; their inherited preventive normalization is not newly certified. Authentic Pasting and SectionPullback module passes do not certify the new LineSquare or downstream packet.

The five repair retains arbitrary finite-free commutative extensions, nonreduced dual test rings, the epsilon-preserving base map and original right tensor algebra. The norm calculation maps hx.symm through the actual dual-base norm, applies the same native algebra equivalence and original coefficient norm. It neither flips tensor actions nor replaces the full all-unit theorem with a pure-tensor-only claim. norm_unit, its original square-zero witnesses and direct ActualDualUnitNormIdentification/FiniteFreeDualTransfer consumers remain unchanged. No added domain, separability, integrality, basis or nonzero condition appears. Absence of a norm_unit hard diagnostic is not a module pass.

Native packet/import/hash/schema/binding checks PASS for 1511 roots and all four present false-alias mutations reject. Every binding and exact source-review companion, current own RESULT/intake identity, native primary and direct-consumer reference is verified. Public statements, definitions, resource/trust options, acceptance flags and full original domains are unchanged. The initial companion checker report-field schema assumption and corrected v2 PASS are preserved without packet edits.

Only metadata-only final attachment is cleared after preserving exact raw reviewed APPs. Sources, intakes, READMEs and obligation text must stay unchanged. The finite-r70 prior success, separate site diagnostics and proposed new conditional joins are outside this verdict. Final staged-tree and hosted verification remain required.
'''}
for lane,t in texts.items():
 j=json.loads((P/(lane+'-PROPAGATION-CHECK.json')).read_text());report=lane+'-PROPAGATION-REVIEW.md';(P/report).write_text(t)
 ev=['check_current_propagation.py','PROPAGATION-TARGETS.json',lane+'-PROPAGATION-CHECK.json',lane+'-PROPAGATION-CHECK.log','check_propagation_review_evidence.py','check_propagation_review_evidence_v2.py','PROPAGATION-REVIEW-EVIDENCE-CHECK.log','PROPAGATION-REVIEW-EVIDENCE-CHECK-v2.log','PROPAGATION-REVIEW-EVIDENCE-CHECK.json','finalize_propagation_reports.py']
 if lane=='PEL':ev+=['PEL-FROZEN-MAP.json','PEL-FIRST-TWO-SOURCE-REVIEW.md','PEL-FIRST-TWO-SOURCE-BINDINGS.json','PEL-PRIME-SOURCE-REVIEW.md','PEL-PRIME-SOURCE-BINDINGS.json']
 else:ev+=['PICARD-GLUING-SOURCE-REVIEW.md','PICARD-GLUING-SOURCE-BINDINGS.json','PICARD-FIVE-SOURCE-REVIEW.md','PICARD-FIVE-SOURCE-BINDINGS.json']
 for row in j['packets']:ev += [str(x.relative_to(P)) for x in (P/'propagation-snapshots'/row['name']).iterdir()]
 j.update(status='PASS_CURRENT_CONTRACT_AND_EXACT_PROPAGATION_ONLY',candidate_hosted_pass=False,review_report={'path':report,'sha256':sha(P/report)},reviewer_evidence={x:sha(P/x) for x in ev})
 dest=P/(lane+'-PROPAGATION-BINDINGS.json');dest.write_text(json.dumps(j,indent=2)+'\n');print(report,sha(P/report));print(dest.name,sha(dest))
