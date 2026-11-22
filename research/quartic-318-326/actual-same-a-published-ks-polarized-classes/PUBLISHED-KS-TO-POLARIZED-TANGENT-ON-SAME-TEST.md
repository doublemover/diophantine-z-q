# The original ordered KS columns on the same polarized dual-number test

## Which published statements give the comparison?

The essential published local comparison is **Lan, Proposition
2.1.5.13** in the author's revised primary text. For an abelian scheme
and an invertible sheaf L, the map from its Lie algebra to the Lie
algebra of its dual obtained by contracting the logarithmic Čech class
of L equals the differential of the homomorphism λ_L induced by that
same L. The proof evaluates the positive-translation square bundle of
Construction 1.3.2.7 on the split dual numbers: in each actual
local line frame the transition is the original unit plus its
derivative, divided by the original unit. Its nilpotent coefficient
is the contracted logarithmic derivative. The Lie identification in
that statement is Lan Corollary 2.1.5.9, using the constant
dual-number test with its distinguished section and ε, and the dual
represents the rigidified class by Theorem 1.3.2.3. Proposition
1.3.2.15(2) gives L on an étale test for the same polarization.

The other required statement is **Yuan v2, §1, definitions of φ₀ and
φ₁**, p. 3 of the PDF. For the actual quaternionic universal abelian
scheme π over its fine model Y, φ₀ is the connecting morphism of the
absolute-to-relative cotangent sequence over the named arithmetic
base. The target is transported to Lie of the **dual of that same
family** tensored with the base differential via the stated canonical
isomorphisms; this is φ₁. This is before the dualizing-line map,
determinant, and polarization in Yuan's construction of ψ₃. Yuan §2.1
fixes the compatible principal polarization, in particular the same
choice of μ. None of the assertions here uses Yuan Theorem 1.1 or its
image estimate as a substitute for the full columns.

Lan Proposition 2.1.7.3, which compares a difference-of-deformations
definition with the extension class only up to convention, cannot on
its own settle the sign. Likewise Lan Proposition 2.3.5.2 is the
PEL quotiented-cotangent theorem and is not the needed signed
class comparison. The following same-stalk calculation fixes the sign
and the exact base comparison rather than importing either proposition
as a pre-normalized ordered matrix.

## Exact application to the two originally ordered columns

Retain the chosen full-frame level-3 genuine model over
S = Spec(Z[1/3]), its original universal family P/Y, its original
compatible principal λ and its actual selected height-one point y.
Use the smooth relative locus: the tame vertical point at 13 or the
smooth generic point of the specified reduced component at 5, **not**
a semistable node traversed by a trait. Let k be the actual residue
field (allow the already selected residue extension), A its actual
marked closed surface, W = Ω_{Y/S}⊗k at y, and v:W→k the same chosen
relative direction. The actual test map ξ:Spec(k[ε])→Y sends a base
coefficient r to its literal value plus ε v(dr), with ε²=0. Its
mark on A and its arithmetic base are unchanged. Do not differentiate
a trait, apply an absolute differential of an imperfect residue
field, or choose another isogenous surface.

Write u₁,u₂ for the original ordered invariant forms of A. A
coherent way to read the residue and field change of Yuan's canonical
Lie target is to apply the same square-zero unit sequence on each
affine test of the abelian scheme. For any affine T mapping into the
base, the constant thickening uses the actual split projection, and
on its unchanged underlying open space the unit kernel is O_{P_T} by
a↦1+εa. This extension of sheaves of abelian groups splits via the
constant coefficient map. Hence its Picard kernel is precisely
H¹(P_T,O), with the split giving the zero point. Rigidification along
the original zero does not change that kernel: an infinitesimally
trivial base line on the affine T is trivial (the same split unit
sequence with affine acyclicity), and different generators are
adjusted by pulling a base unit back to P_T. Its geometric fibres are
trivial, so it belongs to the represented Pic⁰. This is natural on
the actual tests, by pullback of the same units and the same
rigidification. In particular the canonical identification of
R¹π_*O with Lie(P^∨) restricts to the residue identification
Λ:H¹(A,O_A)→Lie(A^∨), and further to the identical field-base-changed
construction. This argument does not need arbitrary base change for
the middle differential sheaf.

For the comparison of connecting maps, lift uᵢ over a neighborhood of
y in the locally free invariant Hodge module and choose local lifts on
one true finite affine cover of P over a small affine base. If the
chosen ordered forms are defined after residue extension, first make
the argument on the residue Hodge module, then extend linearly. By
smoothness of P/Y the original sequence splits locally as modules,
and separatedness gives affine intersections. The Čech difference is
right minus left. After restricting these same lifts to A and
pushing the left coefficient by v, the difference is
f_{i,ab} dε with the original coefficient ε and the original
ordered form. This pushout description uses the same family
P×_Y Spec(k[ε]): on every actual affine a derivation into a B-module
of the pushed-out coordinate ring is a pair of derivations on the two
factors agreeing on base coefficients, and the dual-number factor
differentiates r to v(dr)dε. Thus it uses the original restricted
cotangent row and the **marked** left map, not replacement of that
row by relative differentials over Spec(k[ε]). The resulting class
bᵢ = [f_{i,ab}] equals v(φ₀(uᵢ)) under the actual residue
projection target. The corresponding normalized represented tangent
ηᵢ is Λ(bᵢ), using plus principal units 1+ε f_{i,ab};
there is no negative sign or independent rescaling of ε.

Choose one finite separable K/k over which the same λ has an actual
ample representing line L, and base change **both** ηᵢ and all
other retained data to this K. One nonempty affine étale field
test suffices by Lan 1.3.2.15; any already selected adapted
quadratic residue branch can be enlarged simultaneously.
Put Tᵢ=(dλ)^{-1}ηᵢ in Lie(A_K), which makes sense because the
fixed λ is principal. This determines genuine tangent morphisms
from Spec(K[ε]) into the same A_K. Apply Lan 2.1.5.13 with this single
L. For actual local frames e_b=g_ab e_a of L, the exact conclusion is

    [ { Tᵢ(dlog g_ab) } ] = bᵢ⊗1 in H¹(A_K,O),  i=1,2.

Equivalently the normalized line built by positive translation by
Tᵢ has represented tangent point ηᵢ and the same rigidified line
class as the i-th original directional connecting cocycle. The
classes may be computed on different covers; the assertion is an
equality of cohomology classes, with an actual common refinement
available, not equality of independently chosen overlap functions.

For a matrix check let w_j be the actual ordered dual-family
cotangent basis and let P_λ have column j the coefficients of
λ* w_j in u. If C_{ji}=w_j(Λ bᵢ), evaluation of the original
polarization identity gives the polarized Cpol=P_λ^{-T}C. This is
the ordered pre-determinant output and fixes both indices.
In residue 5 the adapted raw matrix of the fixed nonzero direction
may have rank one and determinant zero. Nothing above turns that
condition into two zero columns or divides by 5. The previously
established rank readouts are separate from this comparison.

## What remains?

There does not appear to be a published statement naming the two
literal original quartic cuts, their chosen y, or their Lean ordered
frame: this last normalization is the explicit same-row calculation
above. No further classical existence/comparison statement about
these two classes is invoked once the genuine selected family,
marked cotangent row and compatible principal polarization are
given; the nontrivial published identification is precisely Lan
2.1.5.13 together with Yuan's definition. A Lean proof must still
realize the actual additive boundary as the same class, with the
original chosen frame and field test, or use a formalized theorem
giving that result. The current literal dlog/overlap sources do
not constitute such a formalization. This is a paper comparison,
not a new native result, determinant argument, or hosted claim.

Primary sources:
- [Lan, author’s revised primary text, Theorem 1.3.2.3, Construction
  1.3.2.7, Proposition 1.3.2.15, Corollary 2.1.5.9 and Proposition
  2.1.5.13 (pp. 127–128 in this version)](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf);
  [book publication record](https://doi.org/10.23943/princeton/9780691156545.001.0001).
- [Yuan, arXiv:2205.11334v2 §§1–2.1](https://arxiv.org/pdf/2205.11334v2).
