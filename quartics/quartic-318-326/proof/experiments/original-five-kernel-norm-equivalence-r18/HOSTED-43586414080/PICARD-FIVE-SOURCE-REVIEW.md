# Independent original dual-algebra norm candidate review

Verdict: no candidate-source preservation blocker found. The current successor application/README contract is not accepted by this source-only report.

Own artifact 14110328931 at run 43586414080/f89bd0a3 was independently checked against GitHub digest, ZIP members, own RESULT/intake and published before source. TensorTraceBaseChange and RightTensorNormTrace pass. Exact new hard errors are failed definitional conversion from inl x to equivalence(x⊗1), then an unspecialized norm equivalence rewrite. Class-reducibility warnings are retained separately.

After 4459f6df357aef89c4b866180268493cf0ae535fa6787fdcf5acf5b468eea5e8, before 4d5e3ae655f503fb76dcb1165137217bff6f0449c056f18746e034ef005275c7, replaces only the failed change with an explicitly typed equality from the actual DualNumberScalarExtension318.equivalence_left and supplies the exact equivalence and argument to both norm_eq_of_algEquiv calls. Pinned Mathlib Norm/Basic.lean, blob 89111f90ee6b682f3fc2737b18b7e9f0364dcc5a, states precisely norm(e x)=norm x with explicit e,x. It is used in its original direction after reversing the known image equality.

The constructed equivalence is the SAME original tensor/dual ring equivalence upgraded over DualNumber R by forward_right. The actualAlgebra uses the original baseMap preserving epsilon, not augmentation. Both arbitrary commutative rings, original R-algebra S, and Module.Free/Finite hypotheses remain; no reducedness, integrality or characteristic assumption is added. The right tensor action, transported finite-free structure, actual coefficient element x⊗1 and complete infinitesimal unit z remain unchanged.

In norm_unit, hz is still the original image equality for that exact z, hn is the unchanged original right-tensor norm/trace theorem, and Units.ext plus infinitesimal_eq identifies the same full dual unit. All public statements, definitions, proof branches outside these rewrites, imports and resource/trust options are byte-identical. Neither determinant norm nor trace is replaced by an arbitrary linear functional or isomorphic target.

ActualDualUnitNormIdentification318.norm_eq directly uses norm_inl on every coefficient unit and norm_unit on every infinitesimal element, then its unchanged uniqueness theorem obtains the original norm on every dual unit. OriginalFiniteFreeDualTransfer318 also consumes the exact identities on original section rings. These published consumers and the original scalar-extension producer were inspected and snapshotted; no downstream pass is inferred.

Exact-delta, own hosted provenance, primary API and source identity checks passed without local Lean. New packet obligations/closure/propagation and hosted full-module/kernel/recursive-axiom acceptance remain pending.
