# Observed original quaternion norm-parity application contract

DRAFT_SOURCE_REPAIR_HOSTED_PENDING for run43572239136 at52ab6e7f. NORM-PARITY-MANIFEST binds identical before/after sources and both character/trace own RESULT/intake/log records. No local Lean. The source and propagation checks do not certify kernel acceptance.

## 1. Native source inputs
Pinned ZMod.Basic145-146 supplies natCast_self n: (n:ZMod n)=0. val_lt61, val_eq_zero489, val_injective626 and val_one_eq_one_mod634 supply an abstract proof that every ZMod2 element equals0 or1 without trying to synthesize a decidable procedure through hidden representations. Existing padicValRat.mul/pow, reducedNorm nonzero and prime facts are unchanged. Current logs prove the old simp procedure loops on word.eq_1 and the closed decide attempt does not synthesize its Decidable instance.

## 2. Actual constructed domain
The domain remains all units Bˣ of the original rational quaternion algebra, including arbitrary rational scalar units and every original integral unit. parity is literally j↦(padicValRat (prime j) (reducedNorm u):ZMod2), so signed integer valuations, including negative valuations, are retained. The target is the original four-coordinate InertiaLabels318.V. No quotient or finite set is substituted for the original domain.

## 3. Coverage and exceptional cases
All four primes, all pairs i,j:Fin4, every q:Qˣ, every norm-one original integral unit and every four-bit label are retained. The prime-injectivity proof now applies norm_num only to goals remaining after fin_cases, avoiding the twelve no-goal errors without skipping any required proof. The bit proof uses val<2 and val≠0 to derive val=1; its zero and nonzero cases exhaust ZMod2. This is not a restriction to selected word labels.

## 4. Maps and exact word order
parity, parityHom, scalarUnit, integralUnit and the original word definition are byte-identical. The ordered product is still rationalUnit0,1,2,3 in that order. The revised proof unfolds word once and rewrites parity_mul before coordinate simplification, rather than feeding word.eq_1 repeatedly to the simp set. No reassociation, commutation or replacement of quaternion units is used. The actual homomorphism into Multiplicative V and its full surjectivity target are unchanged.

## 5. Identity consumed downstream
PELActualOrderNormalizer318.parity is exactly parityHom.comp normalizer.subtype; its parity_word consumes PELQuaternionNormParity318.parity_word (lines49-52) for these actual units. Its scalar parity result lines61-62 consumes parity_scalar. PELFixedNormalizerLift318 consumes parity_norm_one, while PELFixedNormalizerStrictTrace318 uses scalarUnit and parityHom for the same quaternion value. Exact consumer sources are retained. No merely related squareclass or group of the same order is passed onward.

## 6. Downstream statement scope
All public declarations, hypotheses and map definitions stay identical. Proof-only edits affect prime_injective, parity_scalar and parity_word. parity_prime still uses the same injectivity theorem and actual prime norms; parity_surjective still supplies the actual original word. Consumers are not edited. Trace has its own matching failure and predecessor hash, not a sibling pass substituted for evidence.

## 7. Scalars and characteristic two
The scalar norm remains q², giving precisely2*padicValRat(prime j)q. The replacement explicitly rewrites (2:ZMod2)=0 using the pinned characteristic theorem, then zero_mul. It does not assume the rational valuation is zero and preserves negative valuations. Every basis bit and original prime norm is unchanged. Bit normalization is equality in ZMod2, not a Boolean encoding with an unproved bridge.

## 8. Trust and limits
No source imports, resource settings, trust overrides, native evaluator, admission or assumptions change. Existing maxHeartbeats1200000 is unchanged; the recursion issue is addressed by a bounded unfolding/rewrite route rather than a larger limit. The new local classical proof concerns only propositional case analysis in an already noncomputable section, not executable decision computation.

## 9. Evidence and acceptance boundary
Both own hosted logs show twelve no-goal errors, the scalar2=0 disjunction residue, two missing Decidable instances and the recursive word simp. The preceding InertiaRealFixedPoints repair passes individually in both runs, followed by PrimeWord/FivefoldRelation. This new source candidate remains uncompiled. Independent source review must check actual native theorem signatures, original maps, full label coverage and consumer identity; final propagation review and hosted kernel checking remain separate requirements. No full-packet or arithmetic theorem pass is claimed.
