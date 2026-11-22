# Evaluate the same polarization on a dual-number point without constructing a universal line

Fix the original marked abelian surface A and the actual principal
polarization λ at the specified relative smooth point over 13 or over 5.
The field is the actual residue k, not an arithmetic trait. A finite
separable extension k'/k suffices for one genuine relatively ample line
L on the **same** abelian surface to induce λ: use Lan Prop. 1.3.2.15
(étale local existence over a field). This is a permissible single
faithfully flat test, not a replacement of the original surface or of
its marked direction. Choose a generator of e^*L to rigidify L at the
actual zero e. Denote D'=k'[ε]/ε² and let v:Spec D'→A_{k'} reduce to e.

## Exact line and normalization

Write m for the actual group law, p1,p2 for its projections, and s
for the structure map of A×A. On A×A form the square line

    M(L) = m^*L ⊗ (p1^*L)^(-1) ⊗ (p2^*L)^(-1) ⊗ s^*e^*L.

The two zero-axis pullbacks are canonically trivial by the group unit
and the inverse-line contractions; the trivializations agree at the
corner. This is Lan's Construction 1.3.2.7, with the e^*L factor making
the axis normalizations independent of which generator was displayed.
With Lan's convention, the actual represented functor says that this
same square line, viewed over the second factor, defines λ_L=λ; the
first-factor translation is +v, not −v. Pulling back by (id,v) on the
true thickening A_D' gives

    τ_v^*L_D' ⊗ (L_D')^(-1) ⊗ p^*(v^*L ⊗ (e^*L)_(D')^(-1))^(-1),

where τ_v(x)=x+v and p:A_D'→Spec D'. The last factor is a base line
and accounts exactly for rigidification, not an additional A-coordinate
twist. It has no contribution to overlap scalars on A, since the local
test Spec D' admits a single generator that lifts the reduced one.
Consequently this is the actual normalized fiber of the Poincaré line
at the point λ(v), by uniqueness of the represented rigidified class.
A native universal line on all A×A^∨ is unnecessary for this one test.

## Literal coefficient (one actual cover, no artificial frame match)

Take one affine cover of A_{k'} with true L-frames e_a. On overlaps
choose the convention e_b=g_ab e_a, with g_ab the actual unit.
The translation τ_v has identity reduction. Hence the same thickened
opens U_a,D' and all their actual intersections are preserved.
In the literal product chart B_D'=B⊗_{k'}D' of any such open, the
restriction of τ_v on a constant b∈B is uniquely

    τ_v^* b = b + ε D_v(b).

The coefficient is the derivation induced by the entire original group
map: algebra-map additivity and multiplicativity give linearity and
Leibniz, and ε²=0 gives uniqueness. This is the invariant derivation of
the actual tangent, by differentiating the actual group square. Since
all these maps restrict from τ_v, their coefficient derivations
restrict on the same overlap without extra compatibility assumptions.

Use the translated frame tensor the inverse of the old frame and the
single base-line frame. Its transition on the actual overlap is

    τ_v^*(g_ab) / g_ab
       = 1 + ε (D_v(g_ab)/g_ab).

Thus the canonical Lie map for λ represented by L is, on this very
cover, the cohomology class of the contracted dlog transitions.
Changing genuine L-frames e_a to c_a e_a changes g_ab to
c_b g_ab/c_a, and the logarithmic quotient by
D_v(c_b)/c_b − D_v(c_a)/c_a. This is precisely a Čech coboundary
with the same sign convention, not a claim that distinct choices of
frames have the same literal function on all overlaps.

## Scope for the two original KS columns

For each original unpolarized directional column, take its *same*
represented point η_i reducing to the original dual zero, and set
v_i=(λ^{-1})(η_i); λ is the actual principal polarization. The above
line is then the very normalized rigidified class in the former
comparison, after base change k'/k. On the preexisting original KS
cover the actual line class comes from the signed directional
connecting; on this other cover it comes from the displayed dlog
coefficients. Equality is of rigidified classes (or of Čech classes
after refinement), not equality of independently chosen functions.
Faithful flatness detects zero of the original cohomology class
(ordinary field cohomology base change or the reviewed coefficient
reflection), so no rational L over k is required.

This removes only a *native global Poincaré object* from the proposed
local coefficient construction. Existence of the actual polarized
abelian variety, the geometric L by an étale test, and the original
KS-to-same-represented-dual-point interpretation remain genuine
geometric inputs. At 5 the raw directional matrix has rank one (for
the indicated nonzero relative tangent) despite determinant zero.
The construction does not infer that both points or both line
classes are zero. At 13 the nonzero direction has rank two.
No local Lean compilation or new native statement is claimed here.

Primary source: [Lan, Arithmetic compactifications of PEL-type
Shimura varieties, Thm. 1.3.2.3, Construction 1.3.2.7 and
Prop. 1.3.2.15](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf).
