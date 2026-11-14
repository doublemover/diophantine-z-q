# Observed PrimeRightLattice residue-law contract

Exact own run43592150561 at75be14ed, character-r15 and trace-r15 artifacts, sources/digests in PRIME-MANIFEST.json. Candidate3bcda80f is isolated and unexecuted by Lean. The preceding ParityQuotient full-module passes are not acceptance of these new residue proofs.

1. Required input: residueHom needs residue_zero and residue_add for the actual map from Coordinates=Fin4→ℤ to Fin2→ZMod(prime i). The observed add goals retain an unevaluated pointwise sum of residue functions on the right and an integer cast on the left. The candidate first states exactly the two native coordinate casts on the right, then normalizes the complete finite coordinate computations. The zero goal's row selection is now computed for every original i,j.

2. Constructed objects: conjugateCoefficients, rows, residue, Coordinates, product and residueHom definitions remain byte-identical. The map is still the two selected coordinates of the original right product a*bar(n), reduced at the original norm prime. No abstract equal-rank lattice or unrelated matrix replaces the original quaternion order.

3. Coverage: all four indices i:Fin4 and both row positions j:Fin2 are exhausted. The full arbitrary integer-coordinate vectors a,b remain universally quantified. Additivity is not sampled on generators or inferred from numeric tests; the polynomial identity is proved for symbolic a,b in every case. Zero is the exact native zero function in Coordinates.

4. Maps and direction: the explicit change only unfolds residue and the codomain pointwise addition at j. It retains right multiplication by the same conjugateCoefficients i, followed by rows i j, followed by Int.cast into ZMod(prime i). norm_num computes those fixed coefficients and row indices, push_cast transports integer arithmetic through the native cast, and final ring proves each residual. No left/right multiplication switch or reverse quotient map is introduced.

5. Scalars and signs: all original conjugate coefficient vectors, the order basis1,i,(1+j)/2,i/2+k/10, the denominator10, prime table and selected rows remain exact. No sign, factor, prime or valuation is altered. The existing right_norm/left_norm polynomial results and all_divisible proof remain unchanged.

6. Consumer identity: same-file residueHom consumes these exact two laws as map_zero' and map_add'. PELPrimeLatticeResidues318 constructs orderResidue by composing that same residueHom with coordinatesEquiv.symm.toAddMonoidHom; residue_surjective uses its explicit original integer lift. kernel_eq_range uses the exact kernel_iff and rightMultiply on the original order, not just cardinality. These actual direct source passages are retained under primary. No geometric deck-group conclusion or full lattice-index result is claimed here.

7. Exceptional cases: the same original primes and all signed integer vectors, including zero and negative coordinates, remain. No divisibility, nonzero-vector or generic-position premise is added. The complete two-row detection of omitted coordinate divisibility and actual preimage reconstruction remain as before.

8. History/evidence: both own logs show the eight additivity residuals and zero residual at rows i j. Their official artifact metadata/digests and RESULT packet hashes bind the exact published intakes. Candidate changes only the residue_add and residue_zero proof bodies. Primary original product and residue consumer sources are pinned to the same published Git head. Native Int-cast/ZMod source bytes are verified against the pinned mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 tree. Source support is not a compiler outcome.

9. Verification boundary: public statements, imports, definitions, every proof after residueHom, full domains and existing maxHeartbeats remain unchanged. No new axiom/admission, kernel bypass or resource increase. Fresh independent source/contract review and per-packet exact propagation review are required before the next hosted experiment. The candidate is not claimed to pass Lean, a recursive axiom audit or a complete packet, and does not establish the full arithmetic theorem.
