# Observed actual residue-lift simplification contract

Run 43597228569 at 2af419e128047c483b3cdc0ba5e4d65c09d7c4ce. Isolated candidate only, no local Lean. Exact source, own artifacts and pinned APIs are bound in RESIDUE-MANIFEST.json.

## 1. Required source input

residue_lift requires every i:Fin 4 and z:Fin 2→ZMod (prime i). The source proof expands the literal integer lift and actual quaternionic residue rows, moves casts, simplifies the canonical representative cast using ZMod.natCast_zmod_val, and closes ring equalities. The pinned Mathlib theorem requires NeZero modulus; after fin_cases and prime expansion the moduli are exactly 2,3,5,7, all nonzero. No assumption on a particular residue value is supplied.

## 2. Actual construction

liftCoefficients, lift, residue, residueHom, coordinatesEquiv, orderResidue and rightMultiply are untouched. The same integer representatives (z 0).val and (z 1).val and all four literal coefficient matrices remain. There is no substitute free lattice, arbitrary quotient of equal cardinality or reduced set of sample vectors.

## 3. Complete domain

All four prime indices and both output rows are still exhausted by the original fin_cases chain; the entire z vector remains symbolic in its actual ZMod space. The proof is not finite numerical testing of z. No additional side condition, exceptional vector or omitted prime is introduced.

## 4. Maps and direction

residue_lift still states that residue i composed with the exact integer lift is the identity on the entire target. residue_surjective uses precisely that lift; orderResidue is the original residueHom composed with coordinatesEquiv.symm. rightMultiply is actual multiplication by the original integral quaternion element. None of these maps, composition directions or the kernel_eq_range transport change.

## 5. Scalars and signs

Every lift coefficient and quaternionic row/sign remains byte-identical. Integer-to-ZMod casts and canonical natural representative casts are unchanged. The candidate only permits the existing simplifier to make no progress after push_cast when the relevant normal form is already obtained. The final ring tactic remains mandatory on every remaining goal; `try` does not discharge a proposition or admit a proof.

## 6. Downstream object identity

PELPrimeLatticeCokernel318.quotientEquiv uses kernel_eq_range and orderResidue_surjective to identify the literal order/rightMultiply.range quotient with Fin2→ZMod p. Its cokernel_card and literal_indices then concern that same quotient. PELPrimePeriodIsogenies318.exact_rightMultiply explicitly identifies the period-kernel rightMultiply with this exact original map before transporting the quotient. Ramified kernel/division/square and primitive-congruence consumers retain the same residue data. Exact consumer files are preserved, with no claim that this source-only repair establishes their later algebraic or period statements.

## 7. Exceptional cases

Zero residues and all signed integer lift coordinates remain allowed. The four moduli are positive fixed primes, so no zero-modulus exception enters. The original order lattice is neither rationalized nor rescaled, and no part of the target is excluded.

## 8. Observed history

Authentic character-r16 and trace-r16 artifacts both report eight `simp made no progress` errors at line23, after PrimeRightLattice318 genuinely passed each full module. The only source change wraps that specific simp call in try; norm_num, push_cast and the following ring remain. This does not presume every resulting residual will close under hosted Lean. Both own ZIP digests, metadata, RESULTs, complete logs and exact published intakes are retained. Pinned ZMod primary bytes and their inherited Git-blob provenance are verified, not reconstructed from memory.

## 9. Verification boundary

All public telescopes, statements, definitions, imports and production limits remain identical. In particular the existing maxHeartbeats 1200000 is unchanged. No axiom, sorry, placeholder or local compiler execution is introduced. Fresh independent source/contract and packet-specific nine-obligation propagation reviews are required before integration. Candidate module/kernel/recursive audit and whole arithmetic theorem acceptance remain unverified.
