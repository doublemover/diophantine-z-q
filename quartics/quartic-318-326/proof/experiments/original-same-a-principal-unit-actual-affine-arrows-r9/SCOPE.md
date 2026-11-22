# Original same-A principal-unit affine arrows r9

The exact official r8 packet passed 20/25 with 322 audited
declarations and 97 verified baseline modules. ConstantAffineCoverProduced
and PrincipalUnitBoundary both compiled. The only attempted failure
was ConstantActualReduction. Four dependents were blocked.

At the two identity sites in that one owner, first prove the correctly
typed coefficient composite equals the ring identity (fst(inl b)=b),
then apply Spec.map_comp and the precise Spec.map_id K as terms.
This replaces a failed generic Functor.map_id rewrite on an actual
Spec identity. At the remaining site use the already accepted two
levels of extensionality (CommRingCat.hom_ext then RingHom.ext);
the pointwise coeffMap_fst beta is unchanged. All 24 other sources,
imports, actual definitions, public statements and 97 baseline module
keys are unchanged. No heartbeat, linter, proof escape or selector-width
change. Scope remains the original signed forward boundary; not KS/Picard
comparison. This packet has only source/planner validation.
