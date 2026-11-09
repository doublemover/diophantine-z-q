# Actual finite quotient orders, ray embeddings and pole preparation

## Historical and source scope

Read COMPLETENESS-ASSEMBLY.md sections6–7 and the precise existing SelectedQuotientOrders, SelectedTraceFromOrders, ContactPatternSupport, MergedContactPrimePattern and ThreeSelectedPolePreparation producers. The historical route requires fixed exclusions, half-point orders, chosen primary/conjugate embeddings, and simultaneous CRT access. It also states the nontrivial Gaussian CM comparison and the weighted prime/order separation input. This packet incorporates the elementary unit, root-existence and actual-order construction portions. It does not replace the historical CM comparison by compactness or infer CRT compatibility from finiteness. Historical justification exists for the overall conditional route; current formal incorporation of its remaining global inputs is pending.

## 1. Variable denominator unit without circular avoidance

Fix an original row j and selected position i. The original nonzero labels make its five coefficients distinct, and Values supplies five positive prime values u+c_i*w². Choose another position l (1 if i=0, otherwise0). The actual selected rational valuation is1 at row_i and0 at row_l, so their difference has valuation0 by the strict ultrametric equality. Its exact difference is (c_i−c_l)*w*w. All integer factors are integral. If the actual valuation of w were nonzero, it would be positive, making the difference positive-valued, a contradiction. The argument includes w=0 through the WithTop valuation: no unsupported finite-valuation subtraction is used. There is no new avoidance condition depending on the later w.

## 2. One prior fixed bound

The natural bound is76176+C.denominator+the sum over three actual scales of (absolute numerator+positive denominator). It depends only on the original labels and clearing factor. A selected prime larger than it divides neither the nonzero scale numerator nor its denominator, nor the positive clearing factor. Rat.num_div_den has direction num/den=q; the rational valuation quotient formula yields0. For negative integer numerators, the proof explicitly transports through negation and natAbs. Scale nonvanishing is supplied by the original fixedRoot product, not assumed anew. Combining the clearing-factor unit with the automatic w-unit gives the exact variable denominator C.denominator*w unit. Hence the previous Avoidance family is constructed at all15 positions from this one prior bound.

## 3. Actual orders, all15 positions, and LCMs

Roots is a dependent family indexed by Fin3×Fin5, with the actual Qp and primality fact at each original row value. Each position has one rho satisfying rho²=2. Its opposite is−rho, with the exact opposite embedding, not a second unrelated choice. primaryOrder and oppositeOrder are precisely SelectedQuotientOrders.order for the actual class of the original half-point R in the actual formal quotient of E/Qp. They are not orders of P=2R or conjectural CM cardinalities.

The existing compact finite-quotient theorem proves each order positive. Finset.lcm_ne_zero_iff gives positive LCMs; dvd_lcm gives every actual order divides its LCM. This constructs the exact198 Orders interface at all15 positions. Repeated rational prime positions are not discarded, since their chosen embeddings can differ. Finite lcm handles the repetition. divides_proposed is only a consumer: if a future comparison proves each actual order divides a proposed CM modulus, the actual LCM divides it by lcm_dvd. Neither coprimality nor residue compatibility follows from this construction, as the exact negative control with both moduli2 demonstrates.

## 4. Actual Qp embeddings from the rational ray

For any prime p≡1 mod8, p is odd. The pinned ZMod.exists_sq_eq_two_iff gives IsSquare(2:ZMod p); its witness equation is2=z*z, explicitly reversed to z²=2. The root is nonzero since p does not divide2. Its canonical natural representative n satisfies0<n<p, and the pinned cast criterion proves p divides n²−2 in Z. Therefore its p-adic integer residual norm is strictly below1. Both n and2 are units by norm_natCast_eq_one_iff and prime coprimality, so the derivative2n has norm1. The exact existing ScalarLocalSquares.square_of_near_square Hensel producer yields a genuine root in Zp and hence Qp. This is not a modular approximation offered in place of a p-adic point.

Every actual positive prime row in the ray1 mod408 is1 mod8, so roots constructs the entire actual15-position family. oriented multiplies each chosen root by a Boolean-selected sign. Difference of squares in the actual Qp field proves any other root equals rho or−rho; all_orientations therefore covers every root family. The constructed roots do not constrain the primary orientation required by future Gaussian CM separation. The opposite remains exactly negative at every position.

## 5. Same source and threshold order

ActualOrderPrimeTrace.selected_trace applies the existing198 theorem with produced Avoidance and Orders, preserving original beta/Lucas labels, a,h,u,w, Pi³, h≠0,1 and actual real guards. preparation_family starts with the existing prepared2/3/17 continuity neighborhoods and obtains their single prior Q before u,w are selected. Later Q|w and the ray give the required small-prime pole depths/squares, while actual selected-place trace supplies square reduced denominators. The original real inequalities0<b<17 remain on the literal stored coordinates190,241,292 of the same witness.

SelectedRayEmbeddings.ray_preparation_family specializes that entire consumer to actual roots from the ray and arbitrary retained orientation signs. There is no post-pattern root-existence or order-divisibility premise. Its h must still satisfy Pi³*minus divisibility, residue1 modulo plus, and the original continuity congruence modulo L. It does not assert such an h exists. All three Prepared predicates retain the same a, labels, h and parameter C u w. No unrelated pole values or rational point producers are substituted.

## Validation boundary

198 exact predecessor sources, five new sources,203 modules and220 baseline dependencies. The exact checker retains all previous source identities and adds11,636 finite prime/w checks, the precise coefficient-difference polynomial, fixed-bound cases, all15-position LCM checks, an explicit incompatible-CRT negative control, and40 unit-derivative Hensel lifts through p^4. These are independent finite sanity checks, not proofs of the universal theorems or p-adic completeness. The source proof uses the pinned genuine Hensel theorem. Hosted elaboration, recursive axiom audit and distinct bounded source review remain separate acceptance stages. No local Lean run or budget increase.

Remaining: compatible selected prime/ray production and Gaussian CM/order comparison/separation; actual real/continuity CRT intersection for those compatible moduli; four rational TwoTwist Realizations and the global rational-anchor principle. Existing real-density and local continuity producers remain unchanged. The only new prime-size condition is fixed before selection; no later adjustment of Q, labels or scales is hidden.
