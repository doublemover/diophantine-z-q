# Existing declaration/API corrections, three sources

FiniteNormalBaseMonogenicSuborder318: Qualify the already intended native class as Module.IsTorsionFree R A. Native minpoly owner opens Module for the same hypothesis; no altered torsion-free property. Additionally qualify the two exact native AdjoinRoot.Minpoly names in embedding_root. All other proofs and actual definitions remain byte-identical. Bound downstream RootPointLift retains its own similar unqualified class and is not silently repaired or declared accepted.

InjectivePrincipalField318: Scoped include hd before powers_units restores original nonzero image premise; scoped include hf before injective restores original map-injectivity premise and intended existing caller argument order. Native lift_injective_iff first branch has goal f a=f b, already furnished by congrArg(toField) followed by coefficient; remove erroneous apply hf there rather than applying an R-valued injectivity conclusion to a K-valued equality. This latter static correction is necessary after resolving the logged binder cascade, not claimed a separate observed error. Second branch still uses hf to rewrite source equality; same localization and map.

AffineQuotientPullback318: Scoped include hJ before ideal_le retains the original equality J=map f I used only in its proof. The existing arrow definition then captures f/hJ through that proof, restoring intended actual public telescope. No proof bodies, maps, quotient ideals or pushout/pullback assumptions changed.

All are own independent inventory compiler errors. Scoped public telescope restoration is disclosed. No candidate compilation or current propagation approval.

R2 preserves R1 locally and binds full pinned AdjoinRoot owner (namespace begins line 59; names at 853/865). This is an observed namespace repair, not assumed cascade resolution.
