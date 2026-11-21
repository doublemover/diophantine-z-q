# Saturated square contact imposes one character balance in every factor

Keep the actual three scales and the shared square-contact construction
of f0016ec0: d=B^N, N>=2, with r prime to B. Here B includes 76176!,
all actual coefficient numerators and denominators, and the nonzero
cross determinants. Take the real t=(r/d)^2 sufficiently large that
each T_j=c_j²t is larger than every real root θ_i of F. This fixes
the *positive sign* of every factor considered below, especially
the root 1/2399.

For every prime l|B, set k_l=v_l(B)>0. The router proof gives

    v_l(T_j)<=−2k_l,        v_l(θ_i)>=−k_l for θ_i != 0.

Thus θ_i/T_j has depth at least k_l and 1−θ_i/T_j is a local
square: at an odd l this is Hensel on the unit near 1, and at 2
it lies in 1+8Z_2 since 76176! gives k_2>=3. Because T_j itself
is square, *each* factor T_j−θ_i is then a local square at every
prime dividing B. The zero root is already a rational square.

Let σ_{ji} be the positive squarefree class of a nonzero-root
factor T_j−θ_i. All its prime divisors are outside B, and

    (σ_{ji}/l)=+1 for every odd l|B,       σ_{ji}=1 mod 8.

This is a separate condition per rational root class, not merely
on the total product F: if two slots are equal in the router
their actual factors differ by a rational square, so use this
same σ once. No cancellation of opposite symbol bits between
two different factors of F meets these equations.

## Forced companions at the three actual scales

In the exact triad 7a159177 the selected prime in each row has
Rational contact root θ=−1 and valuation +1, and all three
selected primes are 3 mod 7. The latter follows already from
their exact Gaussian A=1,B=3 mod 7; it is also recorded in the
replay. For the three corresponding positive factors T_j+1,
the condition at 7 thus gives

    product of (p/7) over its OTHER odd-support primes = −1.

In particular each of the three factors needs at least one
additional 7-nonsquare prime of odd valuation. It cannot be
a different nominated triad prime: each of those belongs to
a different, unique rational root class, by the twelve
distinct root residues at 3162001. Different classes cannot
share an extra ordinary prime either. Hence **at least three
additional distinct odd-support primes** are forced (at least
six in total) for *every* r satisfying these triad congruences
with the symbolic saturated d=B^N. This proves the named
partial support cannot already be complete.

The same argument is a systematic obstruction to a tempting
parametrization: an exact Gaussian ray prime with A=1,B=3
mod 7 is 3 mod 7, so an odd support built only from those
ray primes must have even cardinality *in every factor class*.
In particular the original one-odd-prime-per-factor ray shape
cannot be realized on this saturated primitive square branch
with large real T_j, for any h. This does not disprove the
original non-square numerator prime-pattern route, nor does
it rule out adding properly chosen partner primes.

## A certified finite signature fixture for partner selection

For a nominated set S of candidate support primes one can
compute a binary signature column ((p/l)) at any finite
choice of small primes l|B. Each factor support is a
zero-sum subset of these columns. Mandatory primes give a
specific nonzero right hand side to be canceled by additional
primes *in that same class*. Distinct root classes must use
disjoint supports and allowed root characters. Then impose
the actual orientation/old-anchor CRT clauses, separately.
Passing these finite tests still does not realize the
claimed factorizations at a rational t.

As a bounded exact check, take the 13 originally examined
Gaussian primes in the explicit window
A=57+112k, B_gauss=80+112m, |k|,|m|<=25,
with norm p>76176 and p=1 mod 408. Trial primality and the
fixed window are replayed. For the small character primes

    (5,7,11,13,19,23,29,31,37,41,43,53,61)

the 13×13 binary matrix has rank 13 (exact bit elimination).
Therefore **no nonempty subset of that particular roster** can
be the sole support of any factor class in the saturated
branch, independent of the order filters. In particular
all triad companions cannot be drawn exclusively from that
finite roster. This is a restricted exact exclusion, not
an exhaustive list of possible Gaussian primes.

The original h, labels and triad certificate are unchanged.
No extra prime, complete support, rational PointPair or Lean
result is asserted here.

    python3 -B check_saturation_character_rank.py | cmp - EXACT-GAUSSIAN-ROSTER-CHARACTER-RANK.json
    sha256sum -c SHA256SUMS
