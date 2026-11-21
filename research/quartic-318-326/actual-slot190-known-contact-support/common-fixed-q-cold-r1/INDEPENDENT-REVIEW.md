# Independent cold review: one actual scalar retuned at the fixed q

Reviewed exact note
`1835432ec3a43e7221f0618ca72c97b5d7d9bdec980ada2b0f93293c2fc62691`,
table `5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7`,
and donor script `6ea9dcf152daa35492857df563a530fcc99e4c63ce889ec43949557fcab156f0`.
The original author replay matched the immutable table byte-for-byte.

The independent calculator instead uses weighted Jacobian operations on
the literal curve over the unramified quadratic ring at 1041427,
working modulo q^4. The first return is 347142 with proper-divisor
witnesses at 2, 3, 47 and 1231. Parameter z at that return has depth
one; on the short model the invariant differential is (1+O(z^4))dz,
and the reciprocal chart is −2z+O(z^5). At this odd q the formal
logarithm therefore agrees with z modulo q^4 on the kernel of
reduction. The given center has v(U_h)=2. From the actual J, divide
both U values by q² before taking their ratio; it is 7 mod q² in the
quadratic ring. This reproduces the displayed four exact modular
entries, with delta a nonsquare and the compact radicand a square
unit. A completely separate outward-rounded real calculation using
the alternative x-doubling identity matches the interval in the table.

At the other three non-131 visible primes, preserving h and i modulo
p² times an annihilating order preserves both literal regular chart
values modulo p²: on the smooth model the first p factors send the
kernel of reduction one step deeper, and the old denominators are
units on both arms. The separately retained 131 depth proves the
fourth unit. The small marked Schur calculation is conditional on
one additional prime only; a known principal corner or total
Legendre sign is not evidence of full matrix invertibility.

For the detector part, the actual contact is monic of degree five
and all three fed weights have order three in z=1/t. The literal
chain limits are (1,0), making the actual trace quotient 1/2 and
the leading pole coefficient 1/(4 s_j^12). The old contact-prime
trace-unit argument in the completeness donor is still needed for
the reduced square denominator; the product identity alone does
not guarantee it. The adapted auxiliary Gaussian 1+i ray gives
norm 2 and neighboring unit norms 1 and 5 at q. This is the
right fixed local rule for the canonical negative beta column.
It is conditional on the prime-selection donor at this modified
fixed ray, not implied by an opaque result only at the old i ray.
The argument for detector companions with exactly one prime uses
their actual 2,3 local square conditions, so that prime is 1 mod 24
and reciprocity reads the required q bit correctly; it gives a
failure only in that hypothetical case.

One genuine new scalar with four retained visible rows and an exact
local correction is verified. The previous fixed scalar is not
changed. No complete companion support, completed canonical common
q₀, detector prime tuple, rational point, or paired rank is supplied.

Independent replay:
`python3 -B check_common_fixed_q_independent.py ACTUAL-COMMON-Q-SCALAR-PREFIX.json | cmp - INDEPENDENT-COMMON-Q.txt`.

Independent review, Vesper / high-review-ci.
