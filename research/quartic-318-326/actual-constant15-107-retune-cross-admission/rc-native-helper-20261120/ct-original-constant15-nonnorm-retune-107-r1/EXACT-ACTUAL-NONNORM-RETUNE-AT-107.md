# An exact retune at the same original scalar index that rejects both named admissions

Keep input a=0, the same actual h=473592745039516333133760
and source curve and point, the original anchor setting, and
the previously checked four visible θ primes. This is a permitted
third translated index (not the old index and not the first
denominator-cleared choice). It has the same known full odd
denominator squareclass M=1+2448β and a new exact nonsplit odd
θ factor 107. It rules out the strict Γ receiver and the two
particular named conductor-15 admissions, **not** all isogeny
lifts, all PointPairs, or the old unchanged scalar.

Write i=6¹⁵·3⁶⁵⁵³⁶J for the original translated index,
m₀=i/h, β=204618888056724185 and R=4376874610839020.
For the retune write i*=i·T, m=i*/h. Keep the exact literal
scalar formula

    Q=Norm(U_[i*]P / U_[h]P) / R¹⁵,
    N=Norm(1+U_[h]P²/R),
    W=N²+R Q²,      c=12W/(1+2448β),      δ=1−βc².

## 1. The depth-one formal ratio at the unchanged h

At the good prime 107, 2 is nonsquare and the source is over
the unramified quadratic completion. The original point has
exact residue order 106, which divides the unchanged h.
The associated parameter z=−x/y of [h]P therefore has
v(z)≥1. It is nonzero because the point is nontorsion.

In the short Weierstrass equation negation is exactly z↦−z.
Both the formal [m] power series and the regular chart
U=2y/(x²+(3−√2)²) in that parameter are odd; the first
commutes with group inversion and the second directly
negates with y. Their first coefficients are m and −2.
Since 2 is invertible here, it follows over the integer ring
of the completion that

    [m](z)=m z+O(z³),  U(z)=−2z+O(z³),  U([m]z)/U(z)≡m mod 107².

This is enough at depth **one**, unlike an estimate which
retains the generic quadratic error before using inversion.
Also N≡1 mod107² since U(z) has positive depth and R is a unit.
Norm of the ratio is m² mod107². Thus, for this exact h,

    W≡1+m⁴/R²⁹ mod107².

The integer m≡7429 mod107² gives W≡8153, c≡3405 and
δ≡107 mod107². In particular the stripped unit of δ there
is exactly 1, not just known square. The other two ingredients
are units, and both (5/107) and (e/107) equal −1, where
e=2952271997968816765 is the prior named opposite test.

## 2. Exact simultaneous CRT and a second p-adic verification

Use B=17538019647970835018444217992595396235871190515714
from the earlier h-side numerator bound. Let C be the earlier
odd common modulus of the seven fixed index periods. Then
107 is prime to C and to m₀. Choose T=2ᴮr with

    r≡2^(−B) mod C,   r≡7429/(m₀·2ᴮ) mod 107²,
    0<r<C·107².

In exact decimal this r is
52714716288326393197791295344475142276675138388813012036417514789.
These two congruences preserve every one of the seven old
translated-index remainders and add the exact 107 constraint.
All old formal divisibilities of i/h are retained since T
is an integer. The unchanged h preserves the real margin.
Thus the old source guard, positivity, anchor label form and
square-denominator argument really apply. The numerator
bound at h and the very large v₂(i*) depend only on those
unchanged inputs, so the earlier exclusion of every crossed
odd denominator pole still holds. No full detector tuple or
new rational PointPair is assumed.

The portable replay confirms the formal result by a separate
literal projective Kummer computation over the unramified
residue integer algebra modulo 107⁹. It reduces the retuned
index modulo 106·107⁸, an exact annihilator at that precision,
and computes U_j²=Z/X on [2j]P. At this h its valuation is
exactly 2. Cancelling the common factor 107² in numerator
and denominator of the unit-padded ratio gives the literal
U_i*²/U_h²≡(5861,0) mod107², i.e. m². Taking its norm gives
Q²·R³⁰, and the two independent W values agree.
No affine rational point expansion or norm solver is used.

## 3. Consequences and the next exact conditional scalar matrix

The rational number 7129δ/T_vis in the single fixed admission
norm has odd valuation at 107 and the unramified local √5
character there is nontrivial. It is not even a local norm.
In fact both named admissions fail individually on this scalar:
the named lift (θ,θ,1) is not admitted, and the old class e
fails the opposite local ψ unit condition. The strict Γ
requires θ a √5-norm and is excluded. These statements do
not say that a different full lift or a rational point on
the constant-15 receiver is impossible.

Moreover θ is square at 5, positive and prime to 10, so
(5/θ)=+1 by reciprocity. Since all four former visible
θ primes split √5, and 107 does not, there is at least
one further nonsplit prime of odd θ depth. This particular
retune has **at least six** primes in its θ support, not
the five possible under the earlier conditional theorem.

If there is exactly **one** further θ prime q besides
131,6551,2470991,16782959,107, then q≡23 mod24 since
θ≡1 mod24 and the indicated product is 23 mod24. At 107
the true stripped d-unit bit is 0 since δ/107≡1 and β
is square there. At the twelve old primes all old true
stripped d-unit bits are preserved. Thus each hidden-column
Legendre bit is the true diagonal bit minus the sum of
the other known entries. Its reverse character at q includes
the reciprocity term [−1/p], since q≡3 mod4. The same
transpose-Selmer matrix with this column has exact kernels

    Selφ masks 0,255,16128,16383,
    Selψ masks 0,4709,11674,16383.

The column order is the eight original β primes, four
original visible θ primes, 107, q. Consequently each has
order four in this case. On the ψ side the admitted class
with mask 4709 is the exact integer

    e₂ = 5·17·107·733·1489·6551 = 65029284442765,

which is ramified at 107 and unit at q. Independently of
the number of further primes, {1,e₂} is the set of scalar ψ
masks supported in the thirteen visible columns that survive
all thirteen visible place conditions. Actual admission of
e₂ beyond those rows is not asserted without the exact q
hypothesis or checking all further places.

There is a genuine alternative to merely rejecting the first
named lift. At a formerly hidden prime, replacing (θ,θ,1)
by (θ,θe,e) replaces the relevant local unit character (5/p)
by (5e/p); the fixed-place conditions remain satisfied because
e satisfies all the old visible ψ conditions, and β is square
at the θ primes. In the exact one-further-q case both (5/q)
and (e/q) are −1, since they are −1 at 107 and each aggregate
sign on the old hidden part is +1. Thus the alternative lift
is actually admitted **under that exact remaining-count
hypothesis**. Its independent crossed pairing is a separate
calculation; no arithmetic rank conclusion follows here.
Neither this construction nor the failure it proves is evidence
that other retunes or the unchanged scalar fail that norm.

    sha256sum -c SHA256SUMS
    python3 -B replay_107_retune.py | cmp - EXACT-107-RETUNE-CONTROLS.json
