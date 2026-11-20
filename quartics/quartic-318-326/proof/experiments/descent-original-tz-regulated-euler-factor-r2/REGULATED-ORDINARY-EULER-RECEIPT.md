# Original 318/326, exact local divisor pair and regulated Euler separation

Status: paper argument + staged source-only increment, not compiled, hosted,
or pushed. The Mathlib-only core does not depend on any CRT packet.
The physical adapter is source checked against the unchanged statements of
the prior multi-position CRT; use the narrow reviewed visibility successor
for those prerequisites, not the known hidden-body/parser defects of r1.

## Exact ordinary joint moment position set

Fix one same-x wrap cell of an actual j=0,1,2 ordinary moment (68).
I is every original marked subset position and both coarse copies' actual
cofactor positions when present; slots are I × Bool, where Bool is **which
divisor in the same original square**, not a duplicated spatial row.
For fixed fine and coarse variables the positive forms are W*x+c_i,
where c_i = W*a_i+b_i, and each signed a_i includes precisely its own
integer wrap offset. Each b_i is a unit modulo the same wheel W.
The same x must be used through all positions.

Take a prime p and assign bit pair d_i,e_i to the two slots for p.
For p|W, all units b_i prohibit every nonempty incidence, leaving factor 1.
For p∤W there is an actual root r_i = −gcdA(W,p)*c_i mod p, and if
at least one slot selects p, the proportion of x mod p satisfying all
constraints is 1/p iff all incident rows have the same root, else zero.
Selecting both slots of one row still cuts the residue density exactly
once. For distinct original rows i,j, equality of their roots is
equivalent to p dividing the literal signed difference c_i−c_j.
The empty choice has proportion 1 for both good and bad primes.
Nothing is conditioned on a Gaussian ray or on an independently copied x.

At first use fixed weights z_i,w_i in a characteristic-zero field.
Off/on contributions are 1/−z_i or 1/−w_i respectively in the two slots.
Summing compatible divisor pairs gives exactly

    E_p = 1 + (1/p) sum_{root classes C modulo p}
                  [prod_{i in C} (1-z_i)(1-w_i) − 1]       if p∤W,
        = 1                                              if p|W.

The sum can range over *all* p roots with empty correction zero. Finite
proof: exchange the two bit sums and the single residue average; at
fixed x, off-root positions must both be off, while positions with
root x retain the factors (1-z_i)(1-w_i).
For injective actual roots E_p = 1+(1/p) sum_i [−z_i−w_i+z_iw_i].
In an already specialized distinct integer tuple, all cross-row primes
are confined to the finite union of prime factors of |c_i−c_j| (i≠j).
Outside this set cross-row incidence is impossible but selecting both
slots of a single row still cannot be omitted. Formal noncoincidence
of terminal polynomials is **not** pointwise injectivity: retain the
exceptional evaluated zero-difference tuples, bound them separately
from polynomial grids, and only apply this finite bad set to an
integer-distinct specialization. The already audited fixed-cutoff
argument handles rare collisions uniformly using the same nonconstant
coefficient after translates and wraps; no independent x is added.

## Squarefree signs, finite prime universe and exact regulator

For independent prime choices inside a finite universe S, put
z_i=p^(−s_i), w_i=p^(−t_i). In each slot an assignment forms a
squarefree natural d_i or e_i. The product of its on-signs and powers
is exactly μ(d_i)*d_i^(−s_i) and μ(e_i)*e_i^(−t_i) respectively;
there is no additional squarefree sign or local copy of α log R.
Use CRT on Q=prod_{p∈S}p: normalized residue density for those exact
divisors is the product of the local densities above, because every
row constraint decomposes prime by prime and the same residue x mod Q
maps bijectively to its coordinate residues. This remains true when
some p|W and when some prime is unused (unrestricted factor 1).
Distributivity gives exact equality with prod_{p∈S} E_p. This finite
independent table is NOT the original finite d_i,e_i≤R expansion.
Even one position, W=1, z=w=1/p, S={2,3}, and cutoff at 3 give different
fractions: including 6 is permitted in the independent universe but
forbidden by the coupled per-slot cutoff.

For a fixed positive σ and Re(s_i),Re(t_i)≥σ, each nonempty compatible
choice has density at most 1/p. The corresponding absolute local
(nonempty) sum is bounded by

    [ (1+p^(−σ))^(2|I|) − 1 ] / p
      ≤ (2^(2|I|)−1) p^(−1−σ).

Hence finite independent products exhaust the absolutely convergent
regulated multiple divisor series at every fixed positive σ, uniformly
in W, intercepts, and root collisions for fixed |I| and σ. No positivity
of the complex weights is used. The proof uses absolute term expansion
for domination, and does not claim a useful bound uniform as σ tends
to zero. At s=t=0, even a single off second-slot family over squarefree
first-slot d has sum of absolute p-terms proportional to sum 1/p
away from W; unregulated absolute summation is invalid.

Actual χ re-enters by Fourier inversion after weighting χ(u) by exp(u):
for u=log(d)/log(R), put s=(1+iξ)/log(R), with the same inversion for
each slot. Inserting the inverse transform first allows unrestricted
regulated divisor sums, while χ itself restores the cutoff d≤R after
integration (χ(t)=0 for t>1). At fixed R>1 the absolute bound above
and Schwartz decay of the transform justify term/integral interchange
on paper. This is not a replacement of the cutoff by the finite
independent prime universe. The factor outside the sums is exactly
[(φ(W)/W) log R]^|I|, once per original row, not once per slot or p.
Integer CRT interval main 1/Q and weighted rounding from prior
7/0 are identical to this normalized residue density prime by prime.

For the zeta comparison, factor out

    B_p = prod_i [(1-p^(-1-s_i))(1-p^(-1-t_i))
                     / (1-p^(-1-s_i-t_i))].

For noncollision p∤W, E_p/B_p=1+O_|I|(p^(-2)), by the literal
first-order expansion; for a collision p∤W the ratio is
1+O_|I|(p^(-1)). Both assertions uniform on nonnegative real parts
since the denominators are units of modulus bounded below at p≥2.
For p|W the ratio is B_p^(-1); at s=t=0 it is (1−1/p)^(-|I|).
Their product cancels the exact wheel normalization (φ(W)/W)^|I|.
The remaining log powers pair with the scale of the zeta quotients;
the normalized single-position integral uses int_0^1 |χ'|^2 = 1.
For fixed W the omitted baseline varying frequencies have fixed-W
errors; this says nothing about a fixed-y o(1) for the ENTIRE tuple
moment when p>y collisions and good-prime corrections remain.

## Boundaries

Native staged core: exact local bit expansion, mass 0/1/p/1, grouping
and distinct simplification, and finite distribution of independent
prime assignments. Native staged adapter: actual accepted affine
coincidence and physical normalization at p∤W and p|W, and removal
of every p outside the actual signed difference prime set as a
cross-row incidence. The all-prime absolute-convergence proof, its
finite CRT factorization into the regulated global series, insertion
of the smooth transform, zeta asymptotics and the averaged collision
tail are paper here, not native moment producer.

To establish actual native FixedCutoffRate for (68) still needs:
regulated analytic passage with normalized logarithmic main factor and
uniform transform/zeta tail; then exclusion of zero differences and
collision averaging with the true two-block widths and all bounded
wraps, allowing e(y)→0 after the fixed-y N threshold. Earlier audited
paper references Tao–Ziegler 2008 §§10.4–10.5 and Appendix E
(https://arxiv.org/abs/math/0610050) for the ordinary divisor calculation,
and the exact Appendix A of Tao–Ziegler 2018
(https://doi.org/10.1017/fmp.2017.3) for (68) and its finite scope.
This is not a proof of PET, of the nonlinear pointwise generalized von
Neumann result, of Chebotarev prime-ray correlation, or of the quartics.
