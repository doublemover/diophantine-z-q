# Independent source review: scalar pole real-domain tokenization

Reviewer: independent Lean reviewer, run 43539970197 at published head 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. Source/provenance review only; no local Lean/Lake/compiler or mathematical acceptance. No source blocker found. Hosted replay must establish compilation beyond the former parser errors.

## Bound target and evidence

- ScalarPoleRealDomain318 before: ad2fe789df9f4db0ed523915ef3ac9e26ffb9ce600408603513c4e098478b43f
- Candidate: a8a209c8e90bb8176305d780faabcdbf2b8468dd4716a73f767a4a89736d7124
- FORWARD_APPLICATION.md: a893a776a166d66c203d97e26f7dc0b50b4380593fff15548cfdee7c6d159c24
- Descent-r6 intake: 27da92bd91e63babf7bc9e4ad849e4d44457141499d2179901e8b353c0739fd3
- Descent own log: e2f29b2ce620f391e9bfa015dc439fb2004fdaf52dc6b2ba6f4c1ee4c84a88b2
- Descent own RESULT: 49772a2ad401611c73ffb4889f5ffeaeea93cee42da894a2f069027b21ff9aeb
- Weighted-r6 intake: ceab312972ef7dd5a8e0bf1a0daa182eebe56dc07496d591e122e4d34ee3fea9
- Weighted own log: 336dee8e4e0d48a4aec93da7edd5b63e43e25127629bf63eea51ce1c39ea14a9
- Weighted own RESULT: 70d779a1b8b9086afc9c567ab281ab1b9119eabdfd9c10cebf24a81dc4c117b9

Both published predecessor source copies equal the exact before file; both own RESULT packet hashes match their own published intake. Own logs are byte-identical after replacing only the respective packet name. Descent ScalarForwardWitness passed 5.430 s and PoleRealDomain failed 4.427 s; weighted passed 5.880 s and failed 4.978 s, respectively. These are module-level historical results, not candidate success.

## Exact scope and mathematical contract

A byte-level check establishes that the complete change is exactly two occurrences of `10<inputR` replaced with `10 < inputR`. Nothing else changes. The exact log shows PrincipalSeg, unknown nputR and OfNat(Type)10, followed by inequalities missing the intended hr and an absent packed_bound. Thus the intended rational inequality was not previously parsed. The repair restores that precise inequality rather than strengthening a valid premise or replacing the proof.

Both packed_bound and pole_domain still quantify arbitrary Assignment w and integer n, with the same half-trace bounds, strict lower norm bound, upper norm bound and inverseNorm condition. Their conclusions retain the same W in (0,10) and poleInput in (0,17). All constants, powers, denominator operations and tactics are unchanged, including the pre-existing maxHeartbeats 0 setting (not newly added or raised). No nonzero premise, finite sampling or excluded case is introduced.

I read the entire candidate and the unchanged PreparedIntegerSource318.scalar_domain application. It supplies exactly integer_inputR_large after witness_input, detector33/common_bounds, detector37 and hscalar/common_bounds, and inverseNorm_bound with hn1 and hn 1. The returned scalarB is definitionally the same poleInput used by that consumer, not a substitute witness. The same original N,Q,W, quotient and inverseNorm remain in the argument. No other speculative spacing or ScalarCompleteSource edit is included. Both eventual successor closures and ancillary classifications still need separate propagation checks.
