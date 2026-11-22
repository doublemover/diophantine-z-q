# The actual period Jacobian's point-level divisor-line law

Classical proof on the original marked compact curve, with typed
dependency ledger. No Lean proof of Abel's theorem, Picard
representability, principal Cartier gluing, or CI request. No donor,
existing selection, or held packet has been changed.

## The actual map, not an isomorphic substitute

Let X be the smooth proper complex normalization in the whole
original K = AdjoinRoot(pJ N p) over ℂ(J), with primitive
x = AdjoinRoot.root(pJ N p). Let Y = X(ℂ) with its already compared
filled complex structure. J is the projective-base coordinate;
J_X is this X's actual algebraic Jacobian, not the QM A. Fix
the original invariant pullback basis ωᵢ of H⁰(Y, Ω¹) and the
actual Abel basepoint P*. Use V = Fin(g) → ℂ in the dual of
this exact ordered basis. The maps and subgroup are

    Per : H₁(Y, ℤ) →+ V,            Per(γ)ᵢ = ∫_γ ωᵢ,
    Λ := im(Per) : AddSubgroup V,
    Q : V →+ V/Λ,                   Q(v) = class of v,
    q : V →+ J_X(ℂ),                actual exponential in this frame.

The same-object saturation input is Λ = ker(q), with the integer
homology image, not merely real span or finite index. Given this,
strict Quotient2 gives the actual homeomorphism β : V/Λ ≃ J_X(ℂ)
with β(Q v)=q(v) for every v; the group map is the same quotient-kernel
equivalence. No rescaling or later basis change is allowed.

For each P in Y choose a piecewise smooth path γ_P from P* to P,
and set z(P)ᵢ = ∫_(γ_P) ωᵢ. Changing paths changes z(P) by an
element of Λ. The single-point period Abel map is P ↦ Q(z(P)).
For the same pointed a, β(Q(z(P)))=a(P): lift a∘γ_P through q
starting at 0; because q pulls back the actual invariant coframe
to dzᵢ, its endpoint is exactly z(P). This is the ordinary same-q
comparison checked by strict Period6, with the literal filled
comparison needed away from the old modular open. Changing
the basepoint to i merely translates the single-point value;
the translation cancels from equal-degree tuples.

Represent finite integer divisors by Y →₀ ℤ, degree the sum of
coefficients. Define the additive map on its degree-zero subgroup

    AJ_period : Div⁰(Y) →+ V/Λ,
    AJ_period(C) = Q (Σ_P C(P) • z(P)).

It is independent of all point-path choices and the point P*.
It respects multiplicity, so D,E need not be reduced. For
effective divisors of equal degree and any their orderings x_D,x_E,
the literal equation for the ordered map A is

    β(AJ_period(E − D)) = A(x_E) − A(x_D).

An actual ordered collision thus gives AJ_period(E−D)=0.
Coincident support points cancel with their signed multiplicities.

## One imported theorem: analytic Abel, not inversion

Use [Milne, *Abelian Varieties*, I §18, Theorem 18.4, printed p. 72](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=78)
on the compact Riemann surface Y itself. For C=E−D, its zero
period class in the true integral-period quotient is equivalent
to a nonzero meromorphic function h with analytic divisor C.
An identity on the chosen basis is an identity on every form.
For C=0 take h=1. We do not invoke Theorem 18.3 (Jacobi inversion)
or Riemann–Roch. Theorem 18.4 does not give a constructive same-K
readback, native Jacobian scheme, arithmetic-centre result, or
fibre count.

Saturation must be independent: just proving q kills the deck
periods could give a zero class only modulo a larger lattice.
The prior same-J Albanese finite-cover proof gives the genuine
integral equality paper-side, without using Theorem 18.4. Do not
use Abel to prove the saturation for this invocation. If a native
point-level Picard identification of the actual a already existed,
it would give the line law directly, making the analytic route
unnecessary. No such declaration was found in the exact donors.

## New same-field readback by trace moments (no GAGA)

We show that this h is the restriction of a unique H **in the
literal K**, not just some element algebraic over ℂ(J). Write
n=[K:ℂ(J)]>0. Delete from the base ∞, poles of the coefficients
of the same monic pJ, its nonzero discriminant's zeros, omitted
ordinary chart values, and images of poles of x or h. These are
finite sets. On the remaining U, the literal monic chart has
locally n simple inverse sheets P_j(z), and x_j(z)=x(P_j(z))
are precisely the distinct roots of pJ(z,−) on those actual
sheets. This uses the actual full monic opening, not a selected
root chart or only the specialized J=1 fibre.

For r=0,…,n−1 put on U

    b_r(z) = Σ_j h(P_j(z)) x_j(z)^r.

This expression is holomorphic and invariant under every sheet
permutation, hence single-valued. It is not yet an algebraic
field trace of h. At a deleted value b, take local base parameter
u (at ∞, u=1/J). At each point above b, in a local analytic
parameter t the nonconstant finite map has u=t^e times a
holomorphic unit, e>0. A Laurent principal part of h or x
bounds its values by a fixed inverse power of |u| in a punctured
neighborhood. Properness exhausts all sheets over a small
neighborhood of b by these finitely many source neighborhoods.
Thus each b_r has at most pole growth there and extends
meromorphically after removing the bounded singularity of a
sufficiently high u-power times b_r. Meromorphic functions on
ℙ¹(ℂ) are rational: subtract the finite Laurent principal
parts and the polynomial part at ∞, then use compactness on
the remaining holomorphic function. Hence b_r belongs to the
actual base ℂ(J), not just a cover of it.

Now use a matrix formed in that very base:

    T_{rℓ} = Tr_(K/ℂ(J))(x^(r+ℓ)),  r,ℓ=0,…,n−1.

For z∈U this trace specializes to the sum of x_j(z)^(r+ℓ),
as seen by splitting the same finite monic quotient or its
multiplication matrix in the same power basis. Thus T(z)=V(z)ᵗV(z)
for the Vandermonde matrix V(z)_{jℓ}=x_j(z)^ℓ. This is the ordinary
transpose, not a Hermitian Gram. Its determinant is det(V(z))²≠0.
So T is invertible over ℂ(J) and c=T⁻¹b is a vector of true rational
functions in J. The equality can first be read off the nonempty
open where the coefficients are defined; any extra excluded poles
of c are harmless.

Define H=Σ_ℓ c_ℓ(J)x^ℓ in the exact K. At a generic ordinary value
the moment equation gives
V(z)ᵗ(V(z)c(z)−(h(P_j(z)))_j)=0. Invertibility gives equality of
H and h on all actual branches. The identity principle on the
connected filled curve gives equality everywhere as meromorphic
functions, and also uniqueness. This proves the same-field claim
without a new coefficient extension or GAGA.

For divisors retain the classical local analytic/algebraic order
comparison: at a smooth closed point of this X, an algebraic
uniformizer analytifies to a holomorphic uniformizer. For instance
take the smooth one-dimensional étale local coordinate and apply
the complex inverse function theorem, equivalently use the
cotangent identification for analytification. The algebraic unit
in the DVR remains an analytic unit, so the orders agree even
at finite ramification or on the reciprocal chart. This local
comparison is not a result of the existing Lean rational
differential transports, and no local cusp normalization is changed.
Therefore the actual algebraic divisor of H is E−D.

## Exact orientation and boundary

With the positive convention O_X(D) = {f | div(f)+D≥0},
multiplication by H is O_X(E) → O_X(D), since div(H)=E−D.
Thus in the one common line the canonical sections are 1 and
H·1, of zero divisors D and E respectively. For negative
ideals the same H is instead O_X(−D) → O_X(−E).
This is the convention of the canonical effective-divisor section
in [Stacks, Lemma 31.15.10](https://stacks.math.columbia.edu/tag/01X0).
Conversely a same-curve positive-line isomorphism puts the
canonical sections in one line; their ratio has divisor E−D,
so the other direction of Abel and the same β recover equality
of the ordered Abel values. This completes the point-level
equivalence and supplies the anchored-pencil input classically.

Lean already has stock local meromorphic order/divisor for
functions on coordinate subsets, affine class-group/Picard,
Scheme.functionField, and generic covering and singular homology
APIs. Those are not a global field of meromorphic functions on
this Y, integration over its actual homology or an Abel/Picard
theorem. In particular the local factorized-rational divisor API
does not algebraize a function on X. Strict Period6 gives ordinary
same-map and kernel inclusion, Quotient2 gives the actual quotient
once its kernel is fixed, and the marked monic donors fix K.
None supplies analytic Abel or native saturated integral period
identification. The filled comparison, full period saturation,
étale analytic local order comparison, and canonical Cartier
section interpretation are separate classical inputs, explicitly
distinguished from the strict Lean donors below.

If proceeding natively after a precise imported Abel theorem, the
smallest real same-field producer is the power-basis trace-moment
comparison for the literal monic pJ: given the n already rational
moments, recover the K-element and characterize its evaluation
on the full simple-root fibre. Meromorphic extension/rationality of
the moments and analytification of local orders can remain
separate. Do not add a Lean wrapper whose input simply asserts
the entire principal-divisor equivalence.
