# Independent cold review of the actual p=3162001 singleton

Reviewed author manifest SHA-256:
`53291d8a8e20eadc8eb1d82a5d1795da9ae0088172185e573f866d744c85cad3`.
It pins note `1beafde50f900a65f92fcbf6f93dc29d77d37f00a5d5893f18ba1d4b53cbd50d`,
checker `0cad060a96dac5968101f04a8cb02a70b19cc578ae33ce7ffe4404c3fb41d4e5`,
and output `d6a1ea6db2d255d824dca7c371a37e5bcda0dcc95cc2aeafdc0355afc3b39d8c`.
The author checker reproduces the reviewed JSON byte for byte.

Independently replayed the two exact full orders using a left-to-right-independent,
least-significant-bit point ladder modulo p^2, with the two lifted roots of 2.
The primary root 2389553 gives order 98746 and the first formal z is
1023381623650; the opposite root 772448 gives order 791033 and the first
formal z is 6835326019709. The quotient-order tests give nonidentity for every
prime divisor of each order. Exact full orders, not just reduced orders for
2R, are used in the modular progression. The primary order is prime to p and
the chosen h has exact p-adic valuation 3, so the primary [h]R has exact
formal depth 4. In the opposite arm [h-1]R is formal but [h]R reduces to R.
The split norm of U([h]R) therefore also has depth 4, since p is not 41.

Independently checked the CRT for the exact positive new h, H_old | i for the
unchanged J, and all three old inert formal rows modulo q^2: at 53, 131, and
1041427 the old H_old/q points have exactly depth 1 and both old and new h
points have at least depth 2. Translating inside the formal group by a
multiple of q^3 times the order changes U_h by depth at least 4. At depth
2 the fixed U_i / U_h is therefore preserved modulo q^2. Regular compact
rows outside these three use the old retained periods. The outward interval
positively clears the actual 1/100 bound at the very least root; the mod-5
retention certifies nonzero guard inputs for the same literal labels.

At c=1 the displayed square t makes precisely the G2 contact factor simple
modulo p^2, with c and Delta units. Checked the pointwise source statements
for all eight chart leaves, both norm tests, six comparison bounds,
the literal first-107 assignment, and its complete primary positivity and
opposite parity hypotheses. The trace-quotient unit theorem then applies to
this one prime. The exact pole input formula has that unit squared times
the simple contact numerator divided by the unit c^10 Delta^6, hence
v_p(b_190)=1. There is no invocation of a global selected-prime or Values
family here.

**Scope:** this varies h but keeps J and the literal labels. The old finite
scalar rows persist; the old exact scalar does not. There is no guarantee on
other primes of this t, no global square denominator, no new rational
PointPair, no linked four-pole solution, and no new kernel-checked Lean
declaration.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
