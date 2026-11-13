# Exact orientation compatibility, without a common-divisor hypothesis

Research continuation from `34cf73ace4df32be1085cf819ca24c665dc0c7a4`.
This packet changes no accepted Lean source, manuscript, coefficient table, or
historical receipt. It contains a written elementary argument, a factorization-free
finite algorithm, and exact finite-field certificates. Independent source review
is recorded separately. No Lean elaboration or kernel checking was run.

## New results and scope

1. The literal three CRT residues need only
   `gcd(Mplus,L) | (h0-1)`, not the older sufficient assumption
   `gcd(Mplus,L)=1`. The other conditions are made exact below.
2. All paired-order orientations can be solved by a graph with parity edges and
   unary side restrictions. A prime dividing a chosen side at *every* position is
   not required. Nontrivial gcds, rather than factorizations, suffice. Repeated
   original positions are retained.
3. For the four previously constructed **independent** primes, direct arithmetic
   on the literal reduction of `R=(1+sqrt(2),2sqrt(2))` sharpens the unresolved
   opposite-side powers of two to `149, 2986, 24116, 92212`. Affine generation is
   checked independently with Jacobian coordinates. These are finite-field
   orders, not newly kernel-checked native formal-quotient orders.

The fixed Gaussian class theorem remains a separate **external** existence route
with fixed labels, clearing, divisibility modulus, and bound before the analytic
threshold. Neither it nor this solver constructs a fifteen-position numeric
`Values` tuple with successful actual orders. No growing-screen density,
order-distribution estimate, real-orbit hit, or full integer witness is claimed.

## 1. Exact three-residue criterion

Let `Pi,Mminus,Mplus,L` be positive integers and `h0` a nonnegative integer.
Put `A=Pi^3*Mminus` and `B=Mplus`. There is a nonnegative integer `h` with

```
h = 0 (mod A),   h = 1 (mod B),   h = h0 (mod L)
```

if and only if

```
gcd(A,B)=1,
gcd(A,L) divides h0,
gcd(B,L) divides (h0-1).
```

Here `h0-1` is an **integer** subtraction, also when `h0=0`. Positivity excludes
zero-modulus conventions; the native actual orders are already positive.

**Proof.** Subtracting each pair of congruences proves necessity. Conversely,
`gcd(A,B)=1` gives a residue `c` modulo `AB` with residues zero and one.
The integers `gcd(A,L)` and `gcd(B,L)` are coprime and their product is
`gcd(AB,L)`: check the minimum valuations at each prime, using that at most one of
`A,B` has positive valuation. The remaining two conditions therefore imply
`c=h0 (mod gcd(AB,L))`. The two-modulus generalized CRT supplies `h=c (mod AB)`
and `h=h0 (mod L)`. Its period is `lcm(A,B,L)>0`, so adding positive multiples
produces arbitrarily large nonnegative solutions. This is not a real-orbit claim.

For completeness the two-modulus construction used by the checker is explicit.
For residues `a mod m`, `b mod n`, set `g=gcd(m,n)`. A solution exists iff
`g|(b-a)`. Write `m'=m/g,n'=n/g`. If `n'>1`, set
`t=((b-a)/g)*(m')^(-1) mod n'`; if `n'=1`, take `t=0`.
Then `a+m*t` modulo `m*n'` is the unique solution class. All inverses used exist
because `gcd(m',n')=1`.

The strict example `Pi=1,Mminus=3,Mplus=5,L=5,h0=1` has `h=6 mod15`, although
`gcd(Mplus,L)=5`. Thus the earlier coprimality hypothesis is genuinely stronger,
not a disguised equivalent condition. The old theorem remains correct on its
stated narrower domain and is not edited here.

## 2. Complete factorization-free orientation graph

Let `I` be a **nonempty** finite index set. At each position `i`, supply two
positive integers `(a_i,b_i)`. Choosing a bit `s_i` places `a_i` on minus when
`s_i=0`, and on plus when `s_i=1`; `b_i` goes on the other side. Define `Mminus`
and `Mplus` as the LCM of their respective sides. In the intended application
`I=Fin 3 x Fin 5`, `a_i=primaryOrder ... i`, and `b_i=oppositeOrder ... i` for
one and the same `Clearing, Values, Roots`. They are not CM curve counts or
order upper bounds. The result also applies to a four-position demonstration,
but that demonstration is not an original fifteen-position witness.

Construct a graph on the `2|I|` **occurrences**, not just the distinct integers.

* Join the two members of each position with parity 1 (opposite sides).
* Join every distinct pair of occurrences whose integer values have gcd greater
  than one with parity 0 (same side). This includes the two members of the same
  position and occurrences at repeated primes.
* For an occurrence with value `n`, allow side minus exactly when
  `gcd(Pi^3*n,L) | h0`.
* Allow side plus exactly when `gcd(Pi,n)=1` and
  `gcd(n,L) | (h0-1)`.

**Claim.** The graph's valid side colorings are in bijection with all orientations
whose literal three CRT residues have a solution.

**Proof of the cross-order condition.** `gcd(Mminus,Mplus)=1` iff every minus
value is coprime to every plus value. One direction uses divisibility into the
respective LCM. For the other, any prime dividing both LCMs divides some value
on each side, contradicting pairwise coprimality. Thus every shared-factor edge
must have equal colors, and these edges suffice. In particular, an internal
`gcd(a_i,b_i)>1` gives contradictory parity-0 and parity-1 edges; it is not omitted.
The additional condition `gcd(Pi,Mplus)=1` holds iff all plus values are coprime
to `Pi`, exactly the plus-side unary test. Together these are `gcd(A,B)=1`.

**Proof of continuity decomposition.** For positive integers and nonempty `I`,

```
gcd(Pi^3*lcm_i m_i,L) = lcm_i gcd(Pi^3*m_i,L),
gcd(lcm_i n_i,L)      = lcm_i gcd(n_i,L).
```

At a prime `ell`, write `t=v_ell(Pi^3)`, `v_i=v_ell(m_i)`, and `e=v_ell(L)`.
The first identity says `min(t+max_i v_i,e)=max_i min(t+v_i,e)`; the second is
its `t=0` case. These follow from monotonicity and attainment of a maximum on a
nonempty finite set. LCM divisibility into an integer is equivalent to each
member dividing it, including zero or negative target integers. Therefore the
unary tests are exactly the other two conditions of section 1. This proves the
claim in both directions, with every original position retained.

A breadth-first traversal assigns relative colors in each connected component.
An edge contradiction is equivalent to an odd-parity closed walk. Without one,
each component has exactly two possible global flips. An occurrence allowing
only one side fixes its component flip; no allowed sides or conflicting fixes
makes the system empty. Otherwise, if `c` components are unforced there are
exactly `2^c` orientations. The bit at each `a_i` recovers the original root-swap
bit, so there is neither quotienting nor overcounting even when an order is one.

This includes the previous common-prime result: if a prime divides a selected
member at **every** position, all those members are linked by parity-0 edges,
and partner edges bring every occurrence into a single component. Hence at
most two orientations remain, possibly none. Shared-factor connectivity can
also hold without such a single prime; the solver does not assume that shortcut.

## 3. Actual finite-field arithmetic for the four independent primes

The literal curve is `y^2=x^3-D*x`, with `D=(3-sqrt(2))^2`. The literal half point
is `R=(1+sqrt(2),2sqrt(2))`, **not** its double `P`. For a root `r^2=2 mod p`,
we evaluate these same formulas in `F_p`. The short-model discriminant is
`64*(3-r)^6`, nonzero at all four primes. Each claimed order `n` is certified by
`[n]R=O` and `[n/q]R!=O` for every distinct prime factor `q` of `n`. The complete
factorization and nonzero point for each drop are retained. If the true order
were a proper divisor of `n`, it would divide some `n/q`, so these tests prove
exactness in the finite group. Exhaustive trial division certifies the small
prime fields and factors. No CM count formula or guessed divisibility is needed.

| p | root r | order at r | root -r | order at -r |
| ---: | ---: | ---: | ---: | ---: |
| 9649 | 7394 | 149 | 2255 | 2441 |
| 95441 | 84708 | 23833 | 10733 | 2986 |
| 387089 | 29597 | 24116 | 357492 | 97081 |
| 1473041 | 250332 | 367673 | 1222709 | 92212 |

The displayed root orientations are explicit and not silently identified with
any noncomputably chosen p-adic roots. Matching the finite-field calculation to
`SelectedQuotientOrders318.order` still requires the good-reduction map for the
corresponding Hensel lift and its kernel's equality with the native subgroup
`{O} union {|x|_p>1}`. The source definition was inspected and is bound below,
but this packet does not add or kernel-check that bridge. In particular the
older native theorems `order(opposite)|16*m` and `m|order(opposite)` are not
silently replaced by these finite-field values.

As a separate finite arithmetic demonstration, the exact four pairs yield four
orientations when `L=1`, and two each for `(L,h0)=(16,0)` and `(16,1)`. Each has an
explicit least CRT residue and full positive period in the certificate file.
The fixed product is exactly `9649*95441*387089*1473041`, not the original Pi.
Four independent primes cannot supply a genuine original row of five distinct
values. This known exclusion is preserved.

## 4. Reproduce and verify

From this directory, using Python's standard library only:

```sh
python -B check_orientation.py
python -B make_reduction_certificates.py
python -B verify_reductions.py
python -B check_bindings.py
```

`make_reduction_certificates.py` prints deterministic JSON; compare it with
`REDUCTION-CERTIFICATES.json`. `check_orientation.py` independently enumerates
all bits for 46,875 two-position inputs, 1,000 seeded random inputs, and twelve
full fifteen-position inputs, including all 32,768 assignments for the all-one
case. It separately enumerates the actual residue classes for 3,888 small CRT
inputs. `verify_reductions.py` uses a separately implemented Jacobian algorithm,
not the affine producer, checks completeness of the four-position scenarios,
and rejects eight mutated certificates. These are finite diagnostics, not proof
of an external analytic theorem, Lean verification, or whole-proof acceptance.

## 5. Historical and application disposition

Historical justification found: the older exact-divisibility CRT adapter proves
the `gcd(A,L)|h0` repair **under** three retained coprimalities. The original
orientation packet proves the common-divisor two-choice implication. Both were
read at their definitions and consuming statements, not inferred from verdicts.
This new argument strictly broadens the continuity condition and eliminates the
common-divisor prerequisite from finite orientation solving. The previously
published arguments remain unchanged and valid on their stated scopes.

Manuscript disposition: pending, no manuscript application changed. Native Lean
consumer disposition: pending, current `ActualOrderOrientationCandidates318`
still uses its older sufficient `Extra/Compatible` predicate. Replacing it would
require a new Lean theorem/consumer and fresh verification. This packet must not
be reported as closing arithmetic witness construction or a formalization gap.
See `APPLICATION.json` for the nine explicit obligations and exact source
bindings. Its authorship is separate from any review record.
