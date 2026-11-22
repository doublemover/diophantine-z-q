# Actual regular Abel fibres: an anchored pencil, not a second trace route

Source-only dependency audit and classical proof plan. No old Lean source
or selector changed, no claim that the geometric Picard comparison is
native. This argument never calls the local tH / support-ideal / trace lane.

## Objects and exact target

Use the original complex compact normalization X of the literal whole
marked field, its own Jacobian J_X = Pic⁰(X), and the same pointed
degree-one Abel map a(x) = [O_X(x − x*)]. The filled comparison identifies
this map on the ordinary open with the original period primitive and
the **same** exponential of J_X. Write A(x) = Σⱼ a(xⱼ) on the ordered
product X^g. A change of Abel basepoint translates A; we do not make
this change or compare to the QM abelian surface.

Fix the original discarded finite set S of cusps and the actual fibres
over 0 and 1728. Let R consist of ordinary ordered tuples with nonzero
determinant in the actual period derivative. Let G = J_X minus the
image under A of the entire complement of R. In particular every
preimage of a point in G is regular. The endpoint called `hdegree`
in the strict compact-volume theorem is an equivalence of the **full**
ordered fibre with Fin(g!), for each y ∈ G. A chosen arithmetic centre
or a selected inverse branch is not a substitute.

## Shortest special geometric input for uniqueness

For a single reduced ordered tuple x at which the ORIGINAL ordered map
A is locally injective, and any ordered tuple z with A(z) = A(x), let
D = Σⱼ xⱼ and E = Σⱼ zⱼ on this X, counting multiplicities. Supply only:

1. Equality for this actual Abel map gives a same-curve line
   isomorphism O_X(D) ≅ O_X(E), or equivalently two canonical zero
   sections s_D, s_E in one line bundle on X with divisors D and E.
   This needs only the original point-level Picard interpretation;
   no representing Picard functor or symmetric-power birationality.
2. A nonzero section of that same algebraic line has effective
   zero divisor of the same class, hence the ordered zeros have
   Abel sum A(x). This is the converse in the same point-level
   comparison. It does not decree how many points are in a fibre.

These are the precise missing bridge in the native lane. See Milne,
[*Abelian Varieties*, III §§2,5, printed pp. 91 and 103](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=108)
for the canonical map and the fibre's linear system interpretation,
and [Stacks, 33.44.12](https://stacks.math.columbia.edu/tag/0B40)
for the effective divisor of a nonzero section of an invertible module
on a proper integral curve (and the same degree).

## Classical anchored proof with no Riemann–Roch or tH

Suppose E ≠ D. Since D is reduced of degree g and E effective of the
same degree (because it is a length-g tuple, even if it has repeats),
there is an index j with xⱼ not in the support of E. In particular
s_E(xⱼ) ≠ 0.

Take one sufficiently small complex disk around each xₖ, all disks
pairwise disjoint and in the actual ordinary open, and a holomorphic
trivialization of the same line on each disk. Represent s_D and s_E
by dₖ and eₖ in the original local coordinate. Then dₖ has a simple
zero at xₖ. Use the nonzero algebraic sections s_D + εs_E, with
ε a common small complex parameter.

* If eₖ(xₖ) ≠ 0, invert the genuine local holomorphic function
  uₖ = −dₖ/eₖ. It has uₖ(xₖ)=0 and derivative
  −dₖ'(xₖ)/eₖ(xₖ) ≠ 0. Its one-variable local inverse produces
  exactly one nearby zero xₖ(ε), with uₖ(xₖ(ε)) = ε. At the
  distinguished j above, xⱼ(ε) ≠ xⱼ for every sufficiently small
  nonzero ε.
* If eₖ(xₖ)=0, keep xₖ(ε)=xₖ. In the small disk the quotient
  eₖ/dₖ is holomorphic after removing its value at xₖ, because dₖ
  vanishes simply. For small ε the factor 1+εeₖ/dₖ is nonzero
  near that point, so the fixed root there is simple.

The xₖ(ε) are distinct because the disks are disjoint; they tend to xₖ.
The zero divisor of the nonzero section has degree deg(O(D)) = g, so
these g distinct zeros exhaust the entire divisor and all are simple.
There is also a degree-free analytic check of exhaustion if desired:
choose the disks within the inverse charts and their compact
complement; the genuine ratio s_E/s_D on that complement is bounded,
so sufficiently small ε keeps the pencil nonvanishing there.
Neither approach chooses an auxiliary curve, lattice, section
identification, or analytic point.

The resulting ordered tuple x(ε) tends to x and differs from x, but has
A(x(ε))=A(x), since every zero divisor in this pencil has that literal
class in the same Picard group. This contradicts local injectivity at x.
**Thus any fibre having a reduced regular point has just one
effective-divisor preimage, even if nothing is known in advance
about regularity of the other preimages.** In the good fibres this also
implies automatic reducedness of every ordering. This is sharper
and more local than requiring a dense full-fibre inversion theorem.

Reducedness of x is not an extra arithmetic assumption. If two
coordinates of a regular tuple coincide, their transposition fixes x
and preserves A; differentiation kills the nonzero tangent vector
with opposite entries (v,−v) in these slots. This contradicts the
invertible complex derivative in the original local sheet. Equivalently
the two columns in the same cotangent coordinate are equal. The
argument does not rely on the two chosen upper-half-plane lifts
being literally the same point.

## Existence and the special set are different inputs

For g=0 the actual Jacobian and product are both the point; 0!=1.
For g>0, on the actual ordinary open independent global invariant
pullbacks stay independent there, since a relation vanishing on a
nonempty open extends by the identity theorem. Column span selection
then gives one simple ordinary Jacobian point without prescribing its
J-values. The source-only evaluation minor owner below formalizes the
finite linear algebra, but not this same-object global readout.

The actual algebraic A:X^g→J_X is proper, since X^g is proper and J_X
separated (closed graph, then projection). Its image is Zariski
closed. The above one true ordinary inverse sheet gives nonempty
analytic interior in that image. A proper closed algebraic subset
of the smooth connected complex abelian variety has empty analytic
interior; therefore A is surjective on complex points. The remaining
native input for this branch is this genuine algebraic/analytic
dominance comparison of the same A, not a primitive sign or a trace
integrality condition. A bare continuous compact map with one local
inverse would not imply surjectivity.

Now every y ∈ G has a reduced regular preimage. The anchored
uniqueness gives exactly its g! permutations as the full fibre.
Use the already-written point-level reordering consumer just with
the same unique effective divisor on G (no dense auxiliary W is
then needed). Nullness of Gᶜ is not used for this degree argument;
it is separate for the volume theorem. The exceptional set includes
the image of *all* bad tuples, not just the points removed from a
given sheet. The signed paper constructs its openness from
compactness and its nullness from the actual primitive derivative
and masked ordinary-coordinate Sard. Strict discarded-null handles
the coordinate-discard part given the actual cover; it alone does
not choose the entire closed algebraic/analytic bad set.

The actual arithmetic J=1 computations can show an evaluated point
misses the three discarded coarse values. They do not show independence
of g evaluations at such centres, noncriticality of an ordered tuple,
or that the value avoids the image of every bad tuple. No independence,
connected good-open theorem, or arithmetic centre selection is
needed in the anchored proof.

## Lean boundary and pin

Immediate local analytic mechanism is stock: construct the holomorphic
germ of −d/e and use the same complex inverse API as the regular sheet.
[Mathlib 56a005855, InverseFunctionTheorem/FDeriv L118–177](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean#L118)
exposes the actual open partial homeomorphism, right inverse near
the centre, and continuity at the centre. The tiny consumer can
combine g changes of variable without introducing any RR, residue,
obstruction-lifting, or regularity assumptions at discarded points.
Do not write a generic fibre theorem that simply assumes its only
new premise “every equal-Abel collision has a path.”

First genuinely missing original-model arrow remains the comparison
between the chosen pointed J_X(C) Abel map and the canonical effective
divisor sections of O_X(D), including analytification of those
sections in the *same ordinary charts*. Existing original rational/
complex chart restrictions concern Kähler differentials, not general
divisor line sections. Even after that arrow, the compact original
analytic realisation and the actual algebraic A and image comparison
must be supplied at the final receiver. No need to construct all
Picard families or repeat the tH route.
