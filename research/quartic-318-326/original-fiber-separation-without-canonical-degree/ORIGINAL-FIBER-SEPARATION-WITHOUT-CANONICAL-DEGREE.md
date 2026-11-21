# Original J=1 differential evaluations without a canonical degree theorem

Paper argument, not a Lean run. This replaces only the global
canonical-zero-divisor or genus input for selecting the ordered minor of
the exact original compact modular Jacobian. It neither replaces nor
identifies the actual curve, map, stable model, or selected QM surface.

## Object and the single rational function

Let L be a number field containing the complete split original J=1
fiber, and X the actual smooth proper integral compact X₁(M) after
extension to L. Equivalently use the original projective normalization
over L equipped with its modular comparison. Its function field F is
the **whole** original monogenic field, not an irreducible factor chosen
independently. Write J for the given forgetful map X→P¹. Over char 0 it
is finite, nonconstant and separable, its branch values are contained
in {0,1728,∞}, and its ordinary original ring is étale over the literal
R=L[J,1/(J(J−1728))]. Use the same full degree
d=[F:L(J)] = p.natDegree, with p the original derivative-unit polynomial.
The J=1 fiber is finite étale, split, nonempty, of exactly d distinct
L-points (the native whole-fiber source).

Let ω be a global regular differential on this same X and suppose its
literal dJ coefficient vanishes at every point of the J=1 fiber. Since
dJ is nonzero over F, there is a unique a in F such that ω=a dJ. Consider
the single rational function

  f = J (J−1728) a / (J−1).

All factors refer to the same J and F. If ω≠0, then a≠0, because the
differential line is invertible on integral X, and f≠0.

## Exact local check at all closed points (including every cusp)

All orders are the ordinary additive DVR orders at actual closed points.
One may use geometric points after extending to an algebraic closure,
then descend regularity, but this is not necessary in characteristic
zero: finite residue fields over L are separable and dz is a local
differential frame for a local uniformizer z. The following local
calculation is the char-zero case of [Stacks 53.12](https://stacks.math.columbia.edu/tag/0C1B).
It uses no Riemann–Hurwitz degree or genus identity.

* Above a finite branch 0, with e=ord(J)>0, write J=z^e u, u a unit.
  Since e is a unit in the residue field, dJ/(dz) has order e−1.
  The other two scalar factors are units, so ord(f)≥e−(e−1)=1.
* Above 1728, use J−1728=z^e u. Identical conclusion:
  J and J−1 are units and dJ=d(J−1728).
* Above 1, e=1. The actual unramified local parameter is z=J−1
  (up to a unit); dJ has order zero. The specified vanishing of a
  gives ord(a)≥1, and numerator J(J−1728) is a unit. Hence ord(f)≥0.
  This uses all points of the full ordinary fiber, not a sample.
* At any other finite point, J, J−1728, J−1 are units, and the map is
  étale. At a possibly nonrational base closed point use its monic
  irreducible polynomial t=p₀(J) as uniformizer. By separability,
  p₀′(J) is a unit at that point and dt=p₀′(J)dJ. Its pullback is a
  uniformizer under this étale map, so dJ is a local frame. Thus
  ord(f)≥0. No other finite point is assumed L-rational.
* At **each** point above ∞ (every actual cusp), put w=ord(J⁻¹)>0.
  Write J=z^(−w)u. Signed Leibniz gives
  dJ/dz = z^(−w−1)(−w u + z du/dz); the parenthesized term is a
  unit in characteristic zero. Thus ord(dJ)=−w−1.
  Since J−1728 and J−1 both have order −w, the scalar ratio has
  order −w. Therefore ord(f)≥1 at every cusp. No cusp width or
  upper bound for w is required beyond positivity, and no restriction
  at mixed-characteristic places is being smuggled into this generic proof.

The original all-place local-branch donor supplies the same formulas,
including the signed cusp case, with hosted strict inventory 7/7 and
159 declarations (local branch run 44771281611, artifact
14647873272). The generic theory still needs to
identify its DVRs with those of this original compact, not just curves
sharing the letter J. The paper is valid for the actual classical
quotient by analytic local uniformization. The source-only compact and
normalization comparison keeps its own exact boundaries.

## Global regularity; only integral proper is needed

A rational function of nonnegative order at every closed point of a
normal curve belongs to each affine ring and hence glues on the same
curve; cf. the normal height-one intersection in [Stacks 15.24.18](https://stacks.math.columbia.edu/tag/0AVB).
Thus f is globally regular on X. The cusp fiber is nonempty: the
proper nonconstant map has closed image containing the generic point
of P¹. The value of f is zero at any of these cusps. An integral proper scheme over a field has a finite-dimensional **field**
of global functions; [Stacks 33.9.3](https://stacks.math.columbia.edu/tag/0366#lemma-varieties-proper-h0)
applies because X is nonempty, connected and reduced. We do **not**
need the constant field to equal L: any nonzero element of this field
is a global unit, impossible when it vanishes at a closed point.
Thus f=0, hence a=0 and ω=0. The full ordered coefficient evaluations
are injective. The span of their dual linear forms is all of H⁰(X,Ω)∨,
so an ordered nonsingular square minor exists (same existing finite
linear algebra proof). In particular g=dim H⁰(X,Ω)≤d. Neither deg(K_X)
nor Riemann–Hurwitz nor separate genus lower bounds enter this step.

## Exact sufficiency at the original non-CM contradiction

On the same original signed level M=C S², the usual generic
primitive vector degree d is one sign quotient of the primitive
vectors modulo M, hence d≤M² (in fact d≤M²/2). The argument above gives
g≤d≤M². A true surjection J_X→A onto the selected abelian surface
already yields g≥2 if needed for the connected-kernel quotient.

The remaining stable Jacobian proof gives h₊(J_X)≤g log(1727M);
Rémond/Bost on the actual quotient gives b≤g(log(1727M)+3/2).
With exact C=195689447424 and B=11185621387570686764517810,
C²<B≤S and 8·1727·C<B≤S imply g≤S⁵ and b≤3g log S, using log 8>3/2.
This is precisely the input of SELECTED-J1-STRICT-CUT.md (same-E bound
D≤2304n≤S³, one GR isogeny, +64). Its strict endpoint still gives
h([u:v])<S⁶/2 versus the original h([u:v])>S⁶ log 2>S⁶/2.
The sharper genus formula is optional and its removal has no effect on
the selected contradiction or the stable-field choice.

## Native algebra option avoiding coherent cohomology

On the two actual affine normalization charts, an element of F
integral over both L[J] and L[J⁻¹] is algebraic over L:
the coefficients of its monic minimal polynomial over L(J) lie in each polynomial
image, as both are integrally closed; their intersection is exactly L
inside L(J) (multiply by J^deg q and use polynomial reversal).
At a cusp DVR of F, a nonzero element algebraic over L whose image lies
in the ring cannot have zero residue: reduce its minimal polynomial;
the nonzero constant term remains nonzero since the residue map on L
is injective. This proves the needed native obstruction without
formalizing a coherent-cohomology finiteness theorem. The regularity
producer requires exactly the local chart valuations above, not any
canonical degree or global zero bound. A structurally independent
scheme-level endpoint may instead use the actual global-regular
section and the genuine injective cusp evaluation of the constant field.
