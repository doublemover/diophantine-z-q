# Coarse finite height via forward trace of regular forms

Original base 558a130e12a461d9b380b44510d457f0d3d8a29d.
Paper proof and source-only native consumers. No hosted result for this packet.
This replaces only the finite estimate in the same-selected J=Jac X₁(M)
strict-cut proof. The stronger resolved-minor correction remains optional.

## Genuine geometry and the identity on the generic differential

Let the single number field L contain the original ordered j=1 points and
be enlarged as in [Javanpeykar, Theorem 4.3.2](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf#page=31)
for the actual map j:X₁(M)→P¹. Let Y be the resulting finite flat
normalization of the true projective j-line and Z its proper regular semistable
resolution. Let O be the actual finite-place DVR of L. The chosen open
U=Spec A with A=O[J] of the actual base contains the entire j=1 base section.
Thus on this open, Y=Spec B with B the integral closure of A in the **whole**
F=L(X₁(M)), with identical K=L(J) and map J into F. Properness of Z→Y
and identity on the generic fiber are all we use of the resolution map.

Write p:Y→Spec O, f:Z→Spec O, and ρ:Z→Y, so f=p∘ρ.
Finite flat duality for π:Y_U→U and smooth duality for U/O identify
`ω_{Y/O}|_{Y_U}` with `Hom_A(B,Ω¹_{A/O})`, with B acting by
precomposition and finite trace equal to evaluation at 1. This follows
from [Stacks 0FKW](https://stacks.math.columbia.edu/tag/0FKW)
and [Stacks 0AU3](https://stacks.math.columbia.edu/tag/0AU3).
Flatness of B over A removes higher Ext; the base smooth line is shifted
by one. No invertibility of the resulting module over B is required.
The native actual affine adjunction and canonical trace-dJ comparison
prove the ordinary module identification in this description.

Proper duality for ρ, with composition in p∘ρ, gives the counit
`Rρ_*f^!O → p^!O`. On H⁻¹ this is `ρ_*ω_{Z/O} → ω_{Y/O}`;
one can see H⁻¹ directly from the relative-Cohen–Macaulay dimension-one
dualizing complex `ω_{Z/O}[1]` and left exactness of ρ_*.
See [Stacks 0AU5, normalized complexes and trace](https://stacks.math.columbia.edu/tag/0AU5),
[0AWG, proper trace](https://stacks.math.columbia.edu/tag/0AWG) and
[0B6J, flat base-change for trace](https://stacks.math.columbia.edu/tag/0B6J).
The morphism over L is an isomorphism **over the same j-line**; its counit
is the canonical identity after the two generic models are identified,
not a finite degree multiplier. Flat restriction to the generic fiber
commutes with the counit. Neither rational singularities of Y, an
isomorphism ρ_*ω_Z≅ω_Y, Cartier dualizing sheaf on Y, nor `ρ^*ω_Y`
is necessary. In purely codimension-one language the same inclusion
comes by testing Tr(b·form) for every b∈B at principal primes of A:
ρ is an isomorphism at normal height-one points of B, the localized
Hom condition holds on this semilocal chart, and A is their intersection
in K. This second argument also does not require an exceptional divisor row.

On the generic fields, Ω_{F/L} is the F-line with **actual** dJ. The finite
dualizing counit of the *different* map π, not of ρ, is
`Tr_{F/K}(c)·dJ` on `c·dJ`; test against each b∈B to obtain
`Tr_{F/K}(b c)·dJ`. This is the generic finite étale trace
[Stacks 0DWM](https://stacks.math.columbia.edu/tag/0DWM);
the finite-Hom representation is unique by nondegeneracy of the field trace.
The exact native Kähler scalar map takes the literal dJ of A into the
literal dJ in K, and the same field extension normalization takes it into F.
Thus after pushing a Cais section from Z, the coefficient c is precisely its
original generic coefficient in the literal normal-chart embedding, without
a different sign/scalar or a chosen field factor.

## Exact same ordered matrix, before the logarithms

The same affine all-prime trace theorem gives x↦a x sends the
complementary module into B for a=M J(J−1728). Hence the genuine
B-linear functional on Hom_A(B,Ω¹_{A/O}) sends the pushed form of
`ω'_c=Cais(θ_c)` to the regular **function** `a c_c∈B`, where c_c is
the same generic dJ coefficient of that form. Cais Theorem 1.2, (4-1),
and (4-9)–(4-10) identify the actual stable Néron Hodge lattice on this Z,
with Abel–Jacobi generic orientation (the (4-9) map has the opposite sign).
No evaluation in a Néron or Z line fiber is needed here.

Restrict B to the actual ordinary monogenic chart via the already-proved
same-field normal embedding. The integral evaluation r_i:B→O on Y is
the one produced by the exact incoming original center: its field value
equals the same ordinary evaluation β_i. Multiplication by a specializes
to −1727M, with the sign retained before taking norms. Thus the matrix
I_{ic}=r_i(a c_c) is integral, and in L is literally
    I = diag(−1727M, …, −1727M) · m · C_v,
where m is the original ordered dJ evaluation minor of ω and C_v is the
actual right change matrix from ω to the oriented Cais basis. This uses no
choice of local frame u_v, sections of ω_Z⁻¹, smoothness at the chosen
Z points, exceptional negativity, or K-nef estimate. It does not assert
an upper bound for the former stronger minus-cokernel correction.

As det(m)·det(C_v)≠0 and a(1)≠0, integrality of det I gives exactly
    −log |(det(m)·det(C_v))⁻¹|_v ≤ g·(−log |1727M|_v).
The nonnegative optional correction here is that of the cleared matrix I,
not the former unscaled resolved-section matrix. The signed numerator is
never changed to a separate witness for p=2/3/11/157.

## Why this is enough for the original strict proof

Use the rational determinant section α'=(det m)⁻¹∧ω. Its finite
coordinates in the true stable determinant lattice are
`(det m·det C_v)⁻¹`. This has finite support by the global lattice;
no support from an auxiliary resolution-frame matrix is needed. The
same product formula divides by [L:Q] **once** and gives finite contribution
≤g log(1727M). There is no change to the arch determinant evaluation:
in each complex embedding the norm term for α' is log of the determinant
of the same evaluation on an L²-orthonormal basis, so the previously proved
genuine unit-disk Hadamard row gives ≤−(g/2) log π. It cancels
the identical + (g/2) log π shift in h₊ on the actual J. Therefore
h₊(J) ≤ g log(1727M), exactly what the same selected J₁ strict cut uses.
The connected quotient/Bost row and strict (S^6/2) margin are unchanged.
The former correction is not used to prove that displayed bound.

## Native scope and honest remaining input

- `SelectedCoarsePushforwardMinor318.cleared_matrix` (4/0) gives the
  exact integral matrix from the same whole-field compatibility and the
  actual arithmetic/ordinary evaluation; `budget_from_cleared_matrix`
  drops only a nonnegative log correction.
- `SelectedActualCaisPushforwardBudget318.budget_at_original_one` (17/0)
  uses the canonical B-linear finite Hom and the literal trace-clearing
  numerator. Inputs remain the actual stable Hodge basis, canonical forms'
  pushforward with the same generic differential, and the same normalized
  chart/center evaluation. No condition on exceptional orders or any
  separately chosen chart of Z is a theorem argument.
- `SelectedCoarseCommonGlobalBudget318.degree_coarse` (3/0) aggregates
  this estimate under the genuine determinant finite support, once [L:Q].
- Actual proper model, relative dualizing sheaf attachment and duality
  counit geometry, and same Cais/Abel–Jacobi lattice remain unformalized.
  The native source does not prove the classical existence of Z nor infer
  semistability merely from a finite chart. The prior refined route is kept.
