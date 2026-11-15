# Residue lift: explicit concrete carrier revision

Source candidate only. Exact run 43652368511 at published 2e4471d08710d58a1fdc2353b62a30023d88e94e still failed PELPrimeLatticeResidues318 in character19, trace19 and evaluator3. Prior source-only repair was not accepted; actual evaluator modules remain unreached. Exact evaluator error retained.

1. Inputs: Every original i:Fin4 and arbitrary z:Fin2→ZMod(prime i), same original order Coordinates. No new assumption.
2. Objects: liftCoefficients, integer lift, residue and residueHom remain byte-identical. No surrogate lattice or alternate map.
3. Coverage: Four explicit i branches cover primes2,3,5,7; ext and fin_cases cover both coordinates while z stays symbolic. No finite sample or exhaustive enumeration of z substitutes for symbolic algebra.
4. Maps: In each branch only the definitionally equal carrier is made explicit: Fin2→ZMod p, and equality of the original residue i(lift i z) at the same literal index. No cast map or identification is added as a hypothesis.
5. Coefficients: All13 ordinary decide coefficient facts unchanged, including21=0 and -97=1 in ZMod7. Full multiplication, conjugation, rows and integer-val casts remain the original formulas.
6. Exceptions: Every zero/nonzero coordinate and all residue vectors retained. No exclusions, injectivity premise or prime assumption added.
7. Consumer identity: residue_surjective, orderResidue, orderResidue_surjective and exact kernel_eq_range unchanged. The same lift is the preimage producer, not a reconstructed rank/count argument.
8. Propagation: One canonical source must replace all matching copies in future successors; own predecessor intake/RESULT and earlier failed attempts remain immutable evidence. No active copy changed here.
9. Honesty: The actual failed log still displayed z with an unreduced vector-index modulus, unused concrete modular facts and val casts. Explicit concrete carriers target that observed defect. Native exact elaboration, residual algebra and downstream axiom audit are still unobserved; independent source review does not certify Lean acceptance. No local Lean/Lake, resource/trust/admission changes.
