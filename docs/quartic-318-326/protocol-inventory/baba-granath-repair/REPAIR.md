# Baba–Granath: bounded replacement of the product-isomorphism argument

Date: 2026-11-08. Author: /root/restart_group_law. The local maximal-order and Steinitz route was suggested by /root/restart_geometric_model, then derived and written here. This is an authored repair candidate, not an independent acceptance of itself. Contact's objection and geometric's independent map review remain distinct records. No manuscript, historical approval, or shared proof file has been changed.

## Decision and exact scope

The displayed homomorphism in published Proposition 3.7 has degree four. It is not an isomorphism, and the stated injectivity test on curve points is false. However, a different unpolarized isomorphism of the same abelian varieties follows from the degree-four map **together with the actual maximal discriminant-six quaternionic action**. The same replacement works for Proposition 3.8. The argument below recovers the integral CM center and the asserted abstract product, rather than assuming rational CM suffices.

This repairs the particular missing input to Proposition 3.9, relative to the explicitly retained construction of the two points in the polarized locus E6 and the other steps of that proposition. It does not turn the degree-four map into an isomorphism, identify a Jacobian polarization with the product polarization, reperform Proposition 3.9's numerical orientation calculation, or accept the entire six-contact height proof. The separate discriminant-210 five-contact producer is not a consumer of this correction.

## 1. Source and actual objects

The primary source read is S. Baba and H. Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, DOI 10.4153/CJM-2008-033-7. The final PDF is pinned in manifest.json. Published pp.743–744 were read both as images and text; §§2.1 and 3.1–3.3, pp.736–742, were read in text to check the actual moduli locus and the noncircular source of its quaternionic action.

The source fixes B=(2,−3), maximal O=Z[i,(1+j)/2], and μ=2j+ij. Its E6 is the genus-two part of the image of the polarized O-QM moduli curve in A2, not the set of arbitrary abelian surfaces isogenous to a CM product. Theorem 3.4 supplies the Hashimoto–Murabayashi O-QM family; Proposition 3.5 identifies its irreducible Igusa locus, and Proposition 3.6 parametrizes that locus before either disputed product argument occurs.

For the two actual smooth curves C:z²=f(x²), the source's direct Igusa calculations place C in that E6 and give j(C)=−16/27 or 81/64. These membership calculations and the preceding Hashimoto–Murabayashi family theorem are retained inputs, not newly independently proved here. They are logically earlier than the erroneous isomorphism inference. Their consequence used below is concrete: A=Jac(C), with its existing Jacobian principal polarization, admits the prescribed **maximal** O-action. Dropping this hypothesis would invalidate the repair.

For D=−24, put K=Q(√−6), R=Z[√−6], a=(2,√−6), E1=C/R, E2=C/a, and

f(t)=(1+√2)t³−3(7−3√2)t²−3(7+3√2)t+(1−√2).

For D=−19, put K=Q(√−19), R=Z[(1+√−19)/2], E3=C/R, and

f(t)=2t³−3(1+9√−19)t²−3(1−9√−19)t+2.

Both are full rings of integers. The elliptic targets are E=E1×E2 in the first case and E=E3×E3 in the second. Their complex CM scalar ring is R, and End⁰(E)=M2(K). The elliptic CM identifications and class numbers stated on pp.742–743 are retained source inputs. Fresh exact polynomial arithmetic independently checks smoothness, the two quotient j-values, and their agreement with the source; see algebra-check.py/json. It does not by itself prove the elliptic CM classification or genus-two Igusa membership.

## 2. Correct statement about the displayed map

Let f1,f2 be the two elliptic quotient maps, and Φ=(f1,*,f2,*):A→E. Set Ψ=f1*+f2*:E→A. The pullback is the transpose of the norm map under the canonical principal polarizations. Diagonal push-pull is multiplication by two. The off-diagonal maps vanish, since one involution acts as +1 on its own factor and −1 on the complementary factor; Hom of complex abelian varieties has no additive torsion. Thus ΦΨ=[2]E. Both factors are isogenies and have equal degrees, so (deg Φ)²=16 and deg Φ=4.

For a nonzero root a of f(x²), the distinct Weierstrass points (a,0),(−a,0) have the same images under both quotient maps: the invariant coordinates are (x²,z) and (x²,xz). Thus the displayed curve-point injectivity test is also false. This paragraph agrees with, but is not the acceptance record replacing, geometric's separate independent map review.

In characteristic zero, the analytic map of an isogeny is an invertible complex-linear map F:C²→C². For period lattices ΛA,ΛE, the sublattice Λ′=F(ΛA)⊂ΛE has **index four**, equal to deg Φ, not the square root of that degree.

## 3. Recovering the full integral CM center

Transport the scalar K-action on E back through Φ in the isogeny category. It is the center of End⁰(A), since End⁰(A)≅End⁰(E)=M2(K). In particular it commutes with the actual left B-action. Its complex action is scalar, with the same chosen CM embedding on both coordinates; this is inherited from the elliptic product through the complex-linear F.

At every odd prime ℓ, F identifies ΛA⊗Zℓ with ΛE⊗Zℓ, because its lattice index is four. The scalar R⊗Zℓ therefore preserves ΛA⊗Zℓ.

At 2 the argument uses the actual maximal O-action, not Φ alone. Write D=B⊗Q2. Since disc(B)=6, D is division. H1(A,Q2) has dimension four over Q2 and is a unital left D-module, so it is rank one over D. Identify it with D, and let L=ΛA⊗Z2 be its full O2-stable lattice. Choose x∈L of least division valuation. For every y∈L, yx⁻¹ lies in the valuation ring O2; thus L⊂O2x. Stability gives the reverse inclusion, so L=O2x. Its ring of right multipliers is x⁻¹O2x, a maximal order; equivalently it is the unique valuation maximal order in D under this identification.

The central K2-action belongs to this right D-commutant. For any quadratic field embedded in a local division quaternion algebra, intersection with the valuation maximal order is its full ring of integers: the reduced norm restricts to the field norm, and nonnegative division valuation is exactly nonnegative field valuation. Here K2 is a field in both cases: 2 is ramified in Q(√−6) and inert in Q(√−19). Consequently every element of R⊗Z2 preserves L. No assumption of good reduction at 2, no étale integral model at 2, and no isomorphism Φ on T2 is used.

Combining all primes, each r∈R preserves ΛA: a rational linear map preserves a Z-lattice precisely when it preserves every Zℓ-completion. It is already complex linear, hence an analytic endomorphism of A; the analytic/algebraic Hom equivalence for complex abelian varieties makes it algebraic. This is the same retained equivalence used in the historical geometry A079 report (Milne, Abelian Varieties, Part I, Theorems 2.8–2.9). Conversely, every integral central endomorphism is an algebraic integer in K, hence belongs to R. Therefore

Z(End(A)) = R.

This is the exact missing integral upgrade. A degree-four isogeny without maximal O6-action need not give it: a conductor at 2 could otherwise survive.

## 4. Recovering a different abstract product isomorphism

Now Λ′⊂ΛE is an inclusion of projective rank-two R-modules of index four. Let I be its determinant index ideal, characterized locally by elementary divisors, so det_R(Λ′)=I·det_R(ΛE) as fractional ideals up to the same ambient determinant line. The finite index gives N(I)=4 and I is supported only over 2.

For K=Q(√−6), the unique prime P=(2,√−6) above 2 has norm two and P²=(2). Hence I=P²=(2). For K=Q(√−19), the polynomial t²−t+5 is irreducible modulo 2, so (2) is prime of norm four and I=(2). Thus in both cases I is principal, and Λ′ and ΛE have equal rank and equal determinant ideal class.

The elementary Dedekind-module classification therefore gives an R-linear isomorphism Λ′≅ΛE. For completeness, its rank-two form can be proved as follows. A rational coordinate projection maps a torsion-free rank-two module onto an invertible fractional ideal; its kernel is another such ideal, and projectivity splits this map. Thus M≅I1⊕I2. Choose equivalent coprime integral representatives for these ideals. The sum map I1⊕I2→R is onto, its kernel is I1I2, and its sequence splits, so M≅R⊕I1I2. Two such modules with the same determinant ideal class are isomorphic. Coprime representatives are obtained by the approximation/Chinese remainder property for fractional ideals. No assumption that R is a PID is made, especially in the class-number-two case.

The resulting lattice isomorphism extends to a K-linear isomorphism K²→K², hence to a complex-linear isomorphism C²→C² in the common scalar CM embedding. It induces an analytic, therefore algebraic, isomorphism of unpolarized abelian varieties. Consequently

Jac(C(−24)) ≅ E1×E2, and Jac(C(−19)) ≅ E3×E3.

These are the abstract product conclusions of Propositions 3.7 and 3.8, now established by a different map. Their endomorphism-ring conclusions follow by conjugation with this new isomorphism: End(E1×E2) in the first case and M2(R) in the second. Matrix entries depend on the convention for row versus column action; no identification of the erroneous Φ with an integral matrix-ring isomorphism is asserted.

This is not an isomorphism of principally polarized varieties with the product polarization. The actual Jacobian principal polarization and its fixed O-Rosati datum remain the ones supplied by membership in E6. Replacing them by the product polarization would be wrong.

## 5. Exact Proposition 3.9 consumer

Proposition 3.9 compares the algebraic j of Proposition 3.6 with j_m² on the **same** polarized moduli quotient. Its use of Propositions 3.7 and 3.8 is to identify the two constructed curves as the CM points of orders of discriminants −24 and −19, with their independently computed algebraic values −16/27 and 81/64. The corrected argument restores the full central orders and the same abstract products, so it supplies more than the rational CM-center statement that was available from Φ alone.

For the −24 branch identification there is also a direct check. Choose the actual uniformizing representative A_z=C²/(O·(z,1)ᵗ) from §2.1, which is available because this is a point of the same E6 locus. The recovered integral central √−6 corresponds, on this specific O-lattice, to an integral right multiplier β∈O with β²=−6 and reduced norm six. It normalizes the maximal order: at 2 and 3 every element of the division algebra normalizes its unique maximal order, and away from 2 and 3 it is a unit of the local order. The associated complex point is fixed by this norm-six element, hence by w6. On the full Atkin–Lehner quotient it is exactly the z6 branch orbit described in §3. Thus the value −16/27 is attached to the required orbit, not merely to an unrelated CM surface with an equal rational endomorphism algebra.

For the −19 orientation step, the repaired order is the maximal order of discriminant −19, not a conductor-two order. Identifying its point on the full W quotient with the fixed point of the explicit embedded order used by the source is the source's usual optimal-embedding/CM-orbit input. The standard count gives four points on V (class number one and two local orientations at each of 2 and 3), permuted transitively by W. This count is described to make the precise residual predecessor clear; it is **not** advertised as a fresh primary-source audit of Eichler's entire optimal-embedding theorem. Likewise, the final numerical distinction between j=j_m² and j=16²/(27²j_m²) in Proposition 3.9 is retained, not newly certified by an interval-computation receipt here. The proposed repair does not require an isomorphism carrying the Jacobian polarization to a product polarization to justify either CM order.

Therefore the bounded conclusion is: the specific invalid map inference need not destroy the actual Proposition 3.9 input, because the argument above restores it. A blanket new approval of all of Proposition 3.9 would require either retaining its explicitly named numerical/CM-orbit predecessors under the existing review scope, or separately checking them. Hodge's alternate modular-invariant orientation investigation is separate and is not incorporated as evidence in this candidate.

## 6. Actual V13 use and unaffected route

The active target is manuscripts/quartic_v13.tex, hash 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd. Exact byte excerpts are bound in manifest.json.

* Lines 487–498 require the **specific polarized** maximal O6 datum and normalizer quotient with branch values 0, infinity, −16/27 and indices 4,6,2.
* Lines 575–598 use those ordered branch values for the integral j-coordinate and pullback by J(u)=−57600F(u)²/G(u)⁶. Switching 0 and infinity without also changing the map would not be harmless.
* Lines 607–618 require the same polarized fiber to have the algebraic Igusa tuple at the rational coordinate j=J(u). The repair does not replace this moduli comparison by an equality of rational endomorphism algebras.
* Lines 984–1008 consume the invariant conversion and metric estimates separately. Those estimates are not reviewed here.
* Lines 6868–6943 instead begin the discriminant-210 five-contact route from González–Rotger quotients. The literal 318 height49/8 producer uses that route, not this D6 coordinate. No conclusion about its separate formal PEL realization gap is drawn.

The previously frozen Lin–Yang review remains unchanged. Its retained Baba–Granath predecessor must now be read together with the new source objection, the independent degree review, and this proposed bounded correction; citing Lin–Yang's attribution of the normalized D6 parametrization to Baba–Granath alone is not an independent repair.

## 7. Nine application obligations

1. **Source hypotheses.** Smooth genus-two curves in the actual polarized E6 locus, with maximal O6-action. Membership/Igusa computations and the family theorem are explicit retained inputs.
2. **Constructed objects.** Exactly A=Jac(C(−24)), A=Jac(C(−19)), and their displayed degree-two elliptic quotients; no arbitrary isogenous substitute.
3. **Index/domain coverage.** Both CM curves, every finite prime; odd primes by index four, prime two by the division maximal order. No generalized claim for other discriminants or nonmaximal orders.
4. **Transition maps.** Φ is still the degree-four pushforward map. Its rational inverse transports K; its lattice inclusion has index four. The eventual integral isomorphism is a new map.
5. **Limiting/object identity.** No inverse limit is taken. The same period lattice is followed through rational transport, every local completion, and the global determinant class; the recovered object is A itself.
6. **Coefficient conventions.** Work over C for homology, R=O_K for rank-two lattices, Q2 for the quaternionic local module. Left O and right commuting K conventions are explicit. No Tate twist is involved.
7. **Local conditions.** B6 is division at two; 2 is ramified for −24 and inert for −19. The determinant index is (2) in each case. No reduction hypothesis at two is inserted.
8. **Exceptional cases.** Nonmaximal O action, a split quaternion algebra at two, or a different quadratic field could leave a conductor or nonprincipal determinant obstruction. Product polarization is expressly excluded.
9. **Downstream consumption.** Exact abstract products and optimal central orders used in Prop.3.9 are restored, with the −24 branch orbit directly identified. The other source orientation/numerical predecessors and the V13 polarization interface remain explicitly scoped, not silently reaccepted.

## Acceptance boundary

This authored candidate awaits a non-author decision bound to its exact hash. It offers a repair of the identified inference and a precise downstream account. It is not an erratum issued by the authors, a proof that the original displayed map is invertible, an unconditional re-audit of every predecessor, a Lean theorem, or a change to the manuscript.
