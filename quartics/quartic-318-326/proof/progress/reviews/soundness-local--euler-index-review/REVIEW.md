# Independent actual Euler-index review

PASS. The frozen EulerIndex318.lean was copied and independently rebuilt with strict kernel checking. Recursive axiom collection passed all10 declarations, with only propext, Classical.choice and Quot.sound. Post-build comparison confirms the original and copy have the same hash.

The proof uses the actual distinct prime factors of N, with support p divides R. Their large-prime product divides R by pairwise coprimeness, so no squarefree-R assumption is missing. The small-prime factor is strictly below3; all primes at least13 satisfy the checked32nd-power bound. The bound includes the empty prime set. Multiplication by the nonnegative N and character index t is safe; strictness is taken against a positive cap, so no hidden positivity of N or t is needed by index_bound. The final exponent is exactly97/32 and the next theorem feeds the actual log(6dN) to the49/8 growth bound.

Retained inputs are correctly explicit: actual modular degree formula (or its upper-bound version), conductor bound/support, and character-kernel index at most4608R. The separate NebentypusOrder318 kernel-index theorem supplies the last group-theoretic step from the determinant relation and controlled normal field degree. The actual curve/model and Jacobian metric estimate are not proved by this finite-product packet.

Reproduce with run.sh in this directory. Only the named module was freshly rebuilt; imported checked dependencies were reused.
