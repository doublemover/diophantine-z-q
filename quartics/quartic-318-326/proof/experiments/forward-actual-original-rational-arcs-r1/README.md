# Exact original finite rational-arc decomposition

This reconstructs the literal rational-arc algebra, not the unpreserved historical packet. The preceding 553 source files are byte-identical to the circle-identity candidate except RealDetectorRatios318: its Fin.addCases branches now apply the exact append_left/right equalities explicitly, instead of relying on definitional reduction. This narrow elaboration hardening changes no theorem statement, chart, or hypothesis. They remain pending hosted compilation.

For any nonzero natural q, any integer numerator a (coprime or not), real beta, original finite integer region s, and complex weight w, the actual original exponential sum at a/q+beta is the sum over all q^5 ORIGINAL coordinate residues r of:

  standardCharacter_q(a * Q_kappa(r)) * originalCircleSum(kappa, exactResidueFiber(r,s), w, beta).

The proof factors each positive phase exactly through the genuine ZMod standard additive character, uses the original polynomial's coordinatewise reduction law, partitions the actual finite set by its residue map, and factors only the constant character inside each exact fiber. Distinct points with the same residue retain their separate weights. Modulus one and non-coprime numerators remain covered; modulus zero is excluded by NeZero. The outer set has exactly q^5 elements, independently of whether individual fibers are empty.

This is a FINITE rational-arc identity. It introduces no q^-5 Jacobian or density normalizer: such factors belong to the later scaled integral/Poisson step and must be derived there. No infinite lattice reindexing, Poisson theorem, minor-arc bound, global prime main term, or absolute singular-series convergence is asserted. The positive phase and all original five coordinates remain unchanged.

Regression: 72 independently evaluated cases for both kappa values, moduli1 through4, three signed/zero numerators and three frequencies; exact integer residue compatibility and q^5 counts plus numerical complex-phase checks. These are regression evidence, not mathematical or Lean acceptance. No local Lean was run.
