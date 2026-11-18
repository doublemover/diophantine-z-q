# What exact class transport can lift on the canonical anchored quartic

**Two different conclusions.** The canonical anchored quartic really has
a rational point for each of the constructed substitute poles, even after
transport out of the auxiliary conic criterion. Such poles with prescribed
first squareclass approximate any prepared target simultaneously at **any
finite set of places**. But hitting the *original* global second class by
this unrestricted seed parametrization is equivalent, for nonsquare second
class, to rational solubility of one specified full 2-descent cover. Merely
extending the finite screening precision never supplies that lift.

Notation: b* is a prepared pole in (0,17) with square reduced denominator,
local squares at 2,3,17 and depths at least 3,1,2. Write b*=m v², v>0
rational, m positive squarefree; set c=m/17, β=17m and D*=1−b*/17.
Since m is a local square at 2,3,17, it is coprime to 102 and β is
squarefree and nonsquare. The positive squarefree part θ of D* also gives
the class of (17b*)²D*. Compare **both** canonical classes, not chosen
polynomial representatives.

## 1. Explicit rational point on the specific canonical Γ

For a rational r with r²>9c set

    z=4r/(r²+3c), u=2(r²−3c)/(r²+3c), b0=m z²,
    d=1−b0/17=(r²−c)(r²−9c)/(r²+3c)².

Put θ' equal to the positive squarefree representative of d, with d=θ'e²,
e≠0. The specific fixed-twist quartic at canonical (β,θ') is

    Γ: W²=θ'(s²−βt²)(s²+3βt²).

The following rational point has nonzero W:

    s=u,  t=z/17,  W=4θ'e.

Indeed βt²=b0/17, u²+3βt²=4 and u²−βt²=4d. This is the **historical**
seed construction of ActualPoleConicAnchor318. The new application is
that Γ depends only on the two canonical classes: the very same triple
continues to solve Γ when b=b0X², 1−b/17=dZ² even if b no longer passes
the earlier sufficient conic test. For a literal Classes b the new scales
can be chosen as c_class=zX, d_class=17b·eZ, since 17b=β(zX)².
The nonzero-W anchored constructor and integer-twist rescaling give an
actual Realization at N=βθ', not merely at free n (one ordinate may be
zero). No assertion about the rank of the curve or another torsor follows.

## 2. Exact obstruction to reaching the original second class

For a fixed target with canonical θ>1, the following are equivalent:

* The unrestricted rational seed-and-class-transport construction above
  reaches b* **exactly** for some r (no auxiliary CRT constraints imposed).
* The smooth projective full-cover chart with affine equation

      J²=θ(1−βh²)(1−9βh²)

  has a rational point. This is the earlier full-descent **d=1 split**
  chart, not all lifts of the anchored torsor.

For finite r≠0 put h=1/(17r), so βh²=c/r². The identity

    d(r)=(1−βh²)(1−9βh²)/(1+3βh²)²

shows J=θe(1+3βh²) if d(r)=θe²; conversely e=J/[θ(1+3βh²)].
Because θ>1 is squarefree, h=0 and both infinity points would require θ
square (the leading coefficient is 9β²θ). J=0 would require β square.
These endpoints cannot occur. Positivity gives either r²<c or r²>9c;
the involution r↦3c/r preserves d(r) and z(r), interchanging these
branches. A sign change of r permits r>0. The two now matching *global*
classes give rational X=v/z and Z with Z²=D*/d. Substitution in the
transport identities reaches the true b*: no limiting argument. When θ=1
the earlier square-complement producer already works; we do not silently
apply this finite-parameter equivalence to a rational infinity endpoint.

This compares precisely the old anchored full-split obstruction to this
new packet's transport family. A Cassels obstruction for this full class
rules out this route. It cannot rule out every Γ lift unless the rest of
the full Selmer fiber is separately excluded, nor every unrestricted
two-twist realization at other n.

## 3. Finite-place matching including the actual complement's bad support

Let T be **any finite set** of places. Enlarge it to include infinity,
2,3,17 and all primes dividing m. We construct one seed d with the
same class as D* over every completion in T, but, deliberately, a
different global class. The preceding prescribed-class packet proves
the required 2,3,17 and m-prime seed congruences: v2(r)=3, v3(r)=2,
r≡1 at 17 and every p|m. Both d and D* are local squares at these places
by the preparation bounds and square reduced denominator.

Now p in T outside this list is odd, p≥5, with c a unit. We impose one
open congruence on the integer r.

* **c square unit.** Take a unit p-adic root of c. In its residue class
  r²−c has a simple zero. Choose k=1 if v_p(D*) is odd, else k=2, and
  choose a unit A whose residue equals the unit part of D* divided by
  −8c. Solve r²≡c+p^k A mod p^(k+1) at the simple root. Then
  r²−9c≡−8c and r²+3c≡4c are units. The two numerator valuations sum
  to k, of the right parity, and their unit part has the right quadratic
  character. The denominator is a square. So d/D* is a square in Qp.
* **c nonsquare unit.** Here v_p(D*) is even. If v_p(c v²)<0 it is
  even and equals v_p(D*); a positive v_p(c v²) makes D* a unit. If
  v_p(c v²)=0, the reduction c v² cannot be 1 (v is a unit), so D*
  is again a unit. If the target unit class is square, take r≡0 mod p.
  Otherwise choose its nonsquare unit residue δ. Over Fp consider the
  smooth projective model of y²=δ(x²−c)(x²−9c). The polynomial has four
  distinct geometric roots because p∤6c and p≠2; its double cover of P¹
  is geometrically integral, branched simply at these roots, hence has
  genus one. By the Hasse-Weil bound it has at least p+1−2√p>0 points;
  no rational origin is assumed. There are no Fp-points above infinity
  (leading coefficient δ nonsquare) or with y=0 (c,9c nonsquares).
  Hence an affine x yields the needed nonzero product with nonsquare
  character. Take r≡x. Even if r²+3c vanishes modulo p, its rational
  value is positive, and its square does not affect the Qp class. This
  handles p=5,7 and all unramified good primes without a large-p cutoff.

The bound used is [Poonen, Rational points on varieties, Cor. 7.2.1,
printed p. 206](https://math.mit.edu/~poonen/papers/Qpoints.pdf#page=220).
It applies to the smooth projective geometrically integral model, not
to the singular ordinary plane closure.

Add one split prime q outside T and outside the support of D* (and all
old complement classes if iterating), using any prime factor of
17mH²−1 with H divisible by every excluded prime and 102m. Impose
v_q(r²−c)=1 there: (mH)²≡c mod q and exactly one of q lifts of a
nonzero root modulo q² is forbidden. The other factors are q-units.
CRT consolidates every finite congruence, independently of r being
eventually large positive. Thus v_q(d)=1 forces a global difference.

To approximate the *actual pole* choose X*=−v/z, Z_p²=D*/d at each
p∈T, including a real root; X*≠1. With C=b0/17, the secant through
(1,1) of C X²+d Z²=1 has slope λ_p=(Z_p−1)/(X*−1). As proved explicitly
in the preceding packet, C+dλ_p² cannot vanish there. Weak approximation
at this finite set of places supplies rational λ arbitrarily close to
each λ_p. The rational second intersection supplies X,Z, so b=b0X²
is simultaneously arbitrarily close to b* at T. Choose enough precision
also to preserve XZ≠0, real bounds, local valuations and integrality of
zX at every p|m. All denominator valuations outside m are even. This
preserves preparation, the exact first class, and the marked complementary
class. By §1 the canonical Γ for this substitute has an explicit rational
point. At q its complement differs from D*, so it cannot be the target.

## 4. Sharp test against a historical nonsoluble anchored curve

Prior reviewed synthetic data (not literal indexed source data) give

    m=409·2857·3673·6121·6529=171523458450570241,
    b*=m(204/20491203655)²,   θ=131·577·1367·9133=943689409057.

The earlier Cassels computation found a nontrivial pairing for the
canonical full class, with the entire fixed-first-coordinate difference
kernel zero. Its conclusion is no rational point on Γ_(17m,θ), not
nonexistence at other n. We use that earlier disposition as a *conditional
application* of §3; we have not freshly re-audited or kernel-checked that
historical obstruction. For this very m, prepared poles with **rationally
soluble canonical Γ** occur arbitrarily close to that example at any
prescribed finite set of places, even including its entire bad support.
In the explicit arithmetic check, q=53 distinguishes the constructed
class globally despite agreement at 2,3,17, all five m primes, all four
θ primes, and additional good primes. This rules out promoting even
unbounded precision at a fixed finite list of completions into global
membership for this family. It does not prove that the obstruction also
occurs at any of the original four source poles.

## Historical/application bindings and verification

Historical full d=1 normalization: ONE-SPLIT-CONTRACT.md, digest
daddcd18f23ae404cd83a2e1dd7966a716dbfc59b5fb1697882dadf31ede5052.
Historical fixed-N equivalence: recovery-actual-anchor-integer-twist/
APPLICATION.md, 0d2cedeae39d33f520dfa0ce63f27564d5faf99b3fa089ec11a7251fadd31abf.
Historical seed anchor: recovery-actual-conic-anchor-family/APPLICATION.md,
4f1d08e1655c45a4a5664b60d46ee9d4f4eca434349b4d68a44831c03d2cceae.
Historical synthetic obstruction: recovery-anchor-explicit-pairing-row/
PAIRING.md, f4ca4fddc6afecd93539e71698908a840b9ea1d5ae412ae70160b30b035a7849.
Earlier all-place local solubility of the original anchored quartic:
LOCAL-SOLUBILITY.md digest 29dac40f32521e2ea83d3ab5c197742213c585e5ea8e9648d512b2aefb888ba4.
These are November 17 source packets. No prior acceptance is transferred
to new assertions.

Run `python -B verify.py` to reproduce FINITE-REPLAY.json. It checks
10,128 finite local class cases, a canonical nonzero-W point, the exact
normalization, and all named local squareclasses of the historical
example's new substitute seed. The theorem, not the finite test, gives
arbitrary precision and the universal quantifiers. No Lean execution,
new source occurrence or actual target Sha trivialization is asserted.
