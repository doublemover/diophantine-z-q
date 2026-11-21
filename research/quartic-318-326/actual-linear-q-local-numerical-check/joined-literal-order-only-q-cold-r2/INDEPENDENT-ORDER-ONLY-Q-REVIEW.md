# Independent cold check: one actual order-only denominator place

Reviewed author manifest SHA-256
9a8252df990c1495feb21016fa0b01fe39169dd0a2739a9dc15a642cbe544ec9
at joined-work-20261120/linear-q-literal-order-only-canary-r2,
and paper SHA-256
e45cfbf487f36c8659697632c104e1c5f03b652e43e083a245ce9b236cc87a94.
All author hashes and the exact byte replay pass, including the outward
strict real norm margin at the least positive CRT representative.

The attached independent replay uses ordinary affine and formal group
laws over Z/q² (direct differential translation for a formal point
and secant reciprocity at a near coincidence), instead of the
donor's projective ladder. It uses fast Lucas doubling identities
rather than companion matrix powers. It verifies the exact actual
a=0 J and h lineage, both exact half-point orders by prime-divisor
exclusion, both formal parameters of exact depth one, all original
U,V nonformal chart residues, and the exact P_G,Q_G and three
nonfirst Q_J evaluations. The CRT retains h mod L, with h≡2 at q.
Neither h nor h−1 is divisible by q. The formal chart estimates
use depth one, without importing the selected-contact q³ input.

The literal primary-ratio and common_parameter identities turn
fractions into ratios on the appropriate formal or nonformal arm:
one need not assume integrality of the unused intermediate shift
or anchor denominator. The sign at the nonformal −R arm changes U
but not V. The expressions actually used in the sixteen original
unweighted detector leaves are polynomial in the needed U/V, norm
and ratio inputs. The positive weights are all of depth 3, exactly
as the original valuation identity gives for v_q(T), v_q(Delta),
v_q(F) = −1, −1, −5. Hence both original ordered folds reduce to
1, the actual quotient reduces to 1/2 and all pole depths are +1.

The common unsquared scale vector is (1,Re Z+N Z,N Z), not the
unrelated square-scale API used by author r1. The replay gives
(1,2129462,2940673) mod q=3162001. The true b_j/q strip from the
original square factor is 1/(4 c_j^12 qt), yielding
(2371501,1890761,1500117) at qt≡1. No other place or positive
real detector bound is claimed on the local representative t.

A full linear key would still have to satisfy each exact row relation,
including (p_{j,-1}−u)/q being the literal scale-clearing square and
the other three slopes at the same scale. The local calculation does
not fix q for a new affine prime theorem; fixing it in such a theorem
would make the remaining forms parallel. This is one actual place
of the original shared h, not a numeric complete key, Ready or
rational PointPair, and not a Lean result.

    python3 -B check_order_only_q_independent.py | cmp - INDEPENDENT-ORDER-ONLY-Q-REPLAY.txt

Signed: independent reviewer, 2026-11-21 UTC.
