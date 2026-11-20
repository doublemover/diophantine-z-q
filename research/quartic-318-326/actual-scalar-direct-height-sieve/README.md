# Direct denominator cut for the fixed alternate scalar curve

**Verified finite result.** For the exact original compact scalar at
`a=0`, `h=473592745039516333133760` and the fixed label multiplier
`J` in `derive_scalar_rows.py`, the alternate two-quadric curve
has no rational point with `Y <= 10^15` in the primitive direct chart
`x=X/Y`, `gcd(X,Y)=1`, `Y>0`.

This bound uses the direct ratio in the alternate curve. It is not a bound
in the distinct original one-variable or `k` chart; no containment or
overlap claim between the two searched sets is made. It is not an
obstruction at larger denominators, an all-height result, a PointPair
nonexistence result, or a proof of the original quartics. No Lean run.

Fixed scalar provenance: [literal compact specialization and h/J](https://github.com/doublemover/diophantine-z-q/tree/e2ef09acc3675847eacda95f084c3ae86396c4b5/research/quartic-318-326/actual-scalar-specialization).
Curve provenance: [alternate marked-pair construction](https://github.com/doublemover/diophantine-z-q/blob/527d4f421d526cdbddf0ccd98f27064bf55666a1/research/quartic-318-326/actual-scalar-norm-pair-local-matrix/rc-linked-scalar-norm-pair-r1/ALTERNATE-NORM-PAIR-GENUS-ONE-ROUTE.md).
The source/replay bundle below needs only a local Node.js, Python 3.8+
and a C++17 compiler, without dependencies or repository checkout.

## Finite domain

Write `B=204618888056724185=5·11·17·163·661·733·1489·1861`, an odd
squarefree integer coprime to 3. Let `c` be the actual fixed scalar
coefficient and `D=B*c^2`. The equations are
```
U² + 3B X² = 4 Y²
V² + 3B (X+cY)² = 4 (Y+BcX)².
```
The first conic has the projective parametrization
`(X:Y:U)=(4rs:B r²+3 s²:2(3s²-B r²))`. For `X≠0`,
`r/s=(2Y-U)/(B X)` recovers the parameter. Use coprime nonzero
integers `r,s`, and let `d=gcd(s,B)`, `e=gcd(r,3)`,
`r=e u`, `s=d v`. There is no point at `Y=0) by the first equation
over the reals and then the second equation at the zero coordinates.
If `X=0`, the second equation requires a rational square of
`4-3D`; the exact mod-13 row gives `c=8`, `D=8`, and the nonsquare
unit 6.

At an odd prime dividing `s`, the gcd of `4rs` and
`B r²+3 s²` is supported on `B`, with depth exactly 1, since
`gcd(r,s)=1` and `B` is squarefree. At an odd prime dividing
`r` the only contribution is similarly a single factor 3.
These factors are disjoint. At 2, the second raw coordinate is odd
if one parameter is even; otherwise it is 4 mod 8 because
`B=1 mod 8`. Thus the gcd is exactly
`ed γ`, with `γ=4` if both parameters are odd, and `γ=1` otherwise.
The reduced coordinates are
```
X = 4uv/γ,   Y = ((B e/d) u² + (3d/e) v²)/γ .
```
Run both signs of `X` with `u,v>0`; `r,s` signs affect only `X`
in the filtered equation. The exact inequalities with the quadratic
form above bound both positive parameters. The 512 candidates
`d|B, e|3` yield 492 nonempty coefficient domains before parity loops.
The independent code uses the integer quotient and integer square root
for each loop inclusive of equality. The original JS also retains the
bound correctly: for this input all numerators and nonnegative weighted
products are at most `4·10^15<2^52`; quotient rounding cannot cross
a whole integer (the gap for a noninteger is at least the reciprocal
divisor), and neighboring squared-integer checks resolve the root.
The real first equation additionally gives `|X|<=2,552,680`.

## Actual modular rows and exclusion

The original script `quartic-2026-11-20-alternate-height-sieve.js` is
paired here with its unmodified sibling, so it checks its expected rows
against the literal scalar evaluator. Do not rely on its fallback
cached table when doing the original replay.

For independence, `derive_scalar_rows.py` constructs the small finite
fields directly. It counts curve points by summing the multiplicities of
squares at each affine abscissa, evaluates the same raw point multiplies
at the literal `h` and `i=6^15·3^65536·J` modulo those group sizes,
and computes the two norms over the split factors or the inert
quadratic field. It does not import the JS, assume a CM order formula,
or use a residue prediction. At a zero of the chart
`U(P)=2 y/(x²+d_curve²)`, where `d_curve=3-sqrt(2)`,
the special ratio for `m=i/h` is computed with the exact translation
sign. On `y²=x³-d_curve² x`, translating by `(0,0)` preserves
`U`, and by either other nontrivial 2-torsion point negates it.
For example for a nonzero root `t` the translated coordinates satisfy
`x'=t(x+t)/(x-t)`, `y'=-2d_curve² y/(x-t)²`, which gives that sign
directly. The chart at infinity is a unit times the formal parameter
(with leading coefficient -2 in the parameter `-x/y`).
Since `m` is even, the shifted point uses the formal multiple,
with derivative `m`; hence the zero/zero ratio reduces to `m` or
`-m` according to the retained reduction. All scalar constants needed
as denominators are units at the 46 primes, and the replay checks that
none of the chart evaluations encounters a pole. All 46 independently
computed `c` residues agree with the original rows.

At each prime use the homogeneous necessary square test
`4(Y+BcX)²-3B(X+cY)²`. Zero is retained. When an actual rational
ordinate squares to an integral local value, the ordinate is integral
there, so reduction is a necessary test even if `p|Y`.
Scaling back to the raw quadratic coordinates multiplies this value
by `γ²` after removing `ed`; `γ` is a unit at every chosen odd
prime. In the independent C++ checker the precomputed table uses
both residues of `u,v` directly, not ratios/inverses.
Rows with `u=v=0 mod p` cannot be primitive and are rejected.
Both signs are propagated together, not chosen separately at each prime.

* Original replay: 492 domains, 716,728,228 positive parameter pairs
  after its early gcd/parity filters, no survivors.
* Independent replay: 492 domains, 830,296,396 positive parity-domain
  pairs, no survivors even before its final primitivity filter. It
  deliberately skips the author's early gcd pruning and hence checks
  a larger set. It still rejects `(0,0)` at a checked prime as noted.

On the audit machine the original replay took 28.35 seconds and
the independent enumeration 21.36 seconds; times are not requirements.

## Replay

Run `sh replay.sh` from any directory. It verifies the exact files,
derives the row table, recompiles the independent checker in a temporary
directory, replays both computations, and compares both transcripts
byte for byte. No outputs overwrite this bundle.
