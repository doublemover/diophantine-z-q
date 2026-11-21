# Exact exclusion over the whole stated bounded fixed-b integer-u slice

Keep the old fixed b=10568037907556089, t=1/2399, λ(u)
=(16u⁴+24u²+1)/(32u²), and the literal nineteen old W mod p²
balls. There is no rational solution of

    W²−t=bY²,       Z²−W²=λ(u)

meeting every required ball for any integer u with
0<|u|≤8,000,000 and gcd(u,102)=1. This strengthens the frozen
17-candidate prefilter without changing any earlier artifact.
It is not a claim about larger u, rational nonintegral u,
u divisible by 2,3,17, varying b, or the final original pole.

## Exhaustion of the potential zero Legendre phases

For each prescribed contact prime let its actual center be W_p
and F_p(U)=16U⁴+(24+32W_p²)U²+1 mod p. For W in that actual
ball, p∤u implies Z²=(F_p(u)+p*integer)/(32u²) mod p,
and 32u² is a square unit since each contact p≡1 mod8.
Hence (F_p(u)/p)∈{0,+1} is necessary. For p|u the same
finitary condition is automatically true because F_p(u)=1;
no missing nonintegral case comes from the denominator.
The integer sign of u is irrelevant, since λ(u) is even.

The existing byte-identical exact C++ wheel checks all positive
odd u≤8,000,000 with 3,17∤u. The script verifies all 19 residues
in its table equal the actual (24+32W_p²) mod p, all primes
are the exact given primes, and the integers are within arithmetic
bounds: the modular products use 128-bit integer, each p<2³⁶.
Its deterministic loop covers the entire range, uses the correct
prime-field exponent, and gives 79 outputs under the **strict**
test that all 19 characters are +1. The compiled small wheel
was replayed locally, yielding exactly the archived 79 bytes.

The missing zero phases are exhausted without repeating this scan:
solve 16s²+A s+1=0 for s=u² mod p at each contact, using
s=(-A±√(A²−64))/32, then both square roots of s and all
integer representatives in the bounded range. The root lists
are checked for distinctness, exact equalities and cardinality
by Euler's criterion for each of the involved quadratic roots.
There are only five admissible u with any zero residue. Each
has a different known contact with character −1:

| u | Some zero contact p | A rejecting contact p |
|---:|---:|---:|
| 1739513 | 8912209 | 415721 |
| 1820905 | 3641809 | 575921 |
| 2409241 | 4818481 | 415721 |
| 5462713 | 3641809 | 575921 |
| 7227721 | 4818481 | 575921 |

Thus the 79 strict outputs already contain every permitted bounded
integer candidate satisfying the necessary contact characters,
even though checking strict +1 alone would not justify this claim.

## Beyond the wheel

Exactly 62 of the 79 have a separate literal p-adic obstruction,
rechecked without trusting a primality list or strength of a norm
heuristic. Every chosen p is odd, prime to 2b·2399, and b is a
nonsquare unit. Then W²−bY²=t a unit forces W,Y integral: the
valuation of that unramified quadratic norm is twice the least
term valuation. In the denominator case p|u, ord λ=−2 ord u,
and its leading squareclass is that of 2. At the reported places
2 is a nonsquare, hence Z²=W²+λ is impossible. In the collision
case p|(λ+t), the identity Z²−bY²=λ+t forces even valuation,
and reducing modulo p forces Y,Z≡0 and W²≡t. The exact list
violates one of these requirements at each specified place.

The remaining 17 exactly partition from the 79 and are the
same parameters excluded by the frozen one-scalar and mixed
affine-lift packets. Nine are globally insoluble, seven conflict
with one fixed original ball, one conflicts with two old balls
jointly, even though their initial local tests passed. This
finishes the bounded exclusion solely for the stated fixed b,t
and integral-u ansatz. No rank or general source theorem.

Reproduce from this directory:

    g++ -O3 -std=c++17 wheel_literal_donor.cc -o /tmp/rc-bounded-old-wheel
    /tmp/rc-bounded-old-wheel 8000000 | cmp - EXACT-WHEEL-79.txt
    python -B check_bounded_wheel_exhaustion.py | cmp - EXACT-BOUNDED-COVERAGE.json

This checks integer C++ and exact Python/SymPy only; no Lean,
hosted test, remote writes, or user-computer actions.
