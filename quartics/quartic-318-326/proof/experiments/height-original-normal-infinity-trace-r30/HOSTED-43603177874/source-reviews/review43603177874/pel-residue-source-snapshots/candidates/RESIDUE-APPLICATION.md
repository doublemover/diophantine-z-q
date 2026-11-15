# Current exact residue lift: post-cast modular coefficient normalization

Run43603177874 at57227e167abe49436d651b932ff75d5bdf9b5898, own character-r17 and trace-r17. RESIDUE-MANIFEST.json binds exact before/after, primary APIs, consumers and all own evidence. Source candidate only.

## 1. Required source input
residue_lift still takes every i:Fin4 and symbolic z:Fin2→ZMod(prime i). Native ZMod.natCast_zmod_val applies to the actual nonzero moduli2,3,5,7. Existing norm_num, push_cast and value simplification produce ring expressions; the candidate first ring-normalizes, then rewrites thirteen explicit closed ZMod coefficient equalities proved by ordinary kernel-checked decide, absorbs a product negation into its coefficient using reverse mul_neg, and uses mandatory ring on every remaining goal. These closed equalities add no caller premise and do not enumerate the arbitrary z vector. The exact generic-norm_num draft is retained as an unaccepted historical snapshot, not silently overwritten.

## 2. Actual construction
liftCoefficients, lift, residue, residueHom, coordinatesEquiv, orderResidue and rightMultiply are unchanged. The same integer representatives (z0).val,(z1).val and all four original coefficient matrices remain. The full original quaternion order, not an abstract rank-four replacement, is used downstream.

## 3. Complete domain
The original fin_cases i, ext j, fin_cases j route retains all four primes and both rows; z remains entirely symbolic. No enumeration of residue samples or restriction on signed lift coordinates replaces the theorem. Every residual is passed to ring_nf, optional progress-only simp on the explicit closed identities, and mandatory final ring via <;>.

## 4. Maps and direction
residue composed with the literal integer lift is still the identity on its entire target. residue_surjective uses exactly that witness. orderResidue composes residueHom with coordinatesEquiv.symm; rightMultiply remains multiplication by the original integral quaternion element. Kernel equality and transport direction are unchanged.

## 5. Exact modular arithmetic
The current failed ring output has coefficients (3,2;4,3) mod2, (4,6;6,8) mod3, negatives9 and4 mod5, and (15,70;21,97) mod7. These are congruent to the required unit/zero coefficients with the exact displayed signs. All original lift coefficients and rows stay byte-identical. The thirteen local equalities are: mod2 2=0,3=1,-3=1,4=0; mod3 4=1,6=0,-8=1; mod5 -9=1,-4=1; mod7 15=1,70=0,21=0,-97=1. Each uses ordinary decide on that closed concrete Fin ring equality, never native_decide or an external evaluator. Reverse mul_neg and zero/subtraction normalization keep every original sign. The simplifier may make no progress, but final ring must close every remaining symbolic goal.

## 6. Downstream object identity
PELPrimeLatticeCokernel318.quotientEquiv uses exact kernel_eq_range and orderResidue_surjective on the literal order/rightMultiply.range quotient; cokernel_card/literal_indices concern that quotient. PELPrimePeriodIsogenies318.exact_rightMultiply identifies the same order map before its period join. The preserved ramified kernel/division/square and primitive-congruence consumers keep their original objects. No new algebraic-isogeny or final arithmetic conclusion is assumed from this repair.

## 7. Exceptional cases
Zero residues, negative integer coordinates and all symbolic values remain included. Fixed positive primes exclude only the already-impossible zero modulus; no new nonzero vector premise or omitted row. All public definitions/telescopes, existing maxHeartbeats1200000, imports and production limits remain identical.

## 8. Current versus historical observation
The previous iteration permitted a no-progress simp with try; that historical code and actual current logs are retained. The current eight errors are unsolved modular coefficient goals, not simp no-progress. RightLattice genuinely passed in both current packets but Residues still failed. This candidate is a fresh normalization route requiring re-review, not a retrospective claim the prior review proved compilation.

## 9. Acceptance boundary
Thirteen closed local coefficient proofs and the explicit symbolic normalization stage replace the unsuccessful generic-normalization draft, whose full prior source/diff/contract/manifest bytes are preserved. All changes are within the proof body of residue_lift. It neither admits a goal nor proves whole packet success by static inspection. Exact current primary/consumer/source/evidence bindings and fresh packet-specific nine obligations must be independently reviewed. No local Lean, candidate kernel/recursive-audit acceptance or complete arithmetic theorem claim.
