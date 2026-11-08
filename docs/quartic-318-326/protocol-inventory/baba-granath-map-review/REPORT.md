# Independent check of the displayed Baba–Granath quotient map

Decision: **the displayed map in the proof of published Proposition 3.7 has degree four, not one. The claimed curve-point injectivity is also false.** This confirms the precise map objection, not a claim that the abstract product theorem or the downstream theorem is false. Reviewer: /root/restart_geometric_model. Original objection author: /root/restart_contact_field. The reviewer read the final published text and rendered printed pages 743–744, then independently checked both arguments below.

## Exact source and version

S. Baba and H. Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, DOI https://doi.org/10.4153/CJM-2008-033-7. Final publisher PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E6B7F5233E98E9C8E013658575FF713F/S0008414X00022008a.pdf/genus-2-curves-with-quaternionic-multiplication.pdf . Its SHA-256 is c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c. Printed p.743 contains the map and proof; p.744 invokes it in Propositions 3.8–3.9. The March 17, 2005 cited preprint is separately pinned, but the present decision rests on the final publisher copy, not merely the preprint.

The precise assertion under review is the source's homomorphism Phi: Jac(C) -> E1 x E2 induced by the two degree-two quotient maps. It is not an arbitrary possible isomorphism of unpolarized abelian varieties.

## Direct counterexample to the curve-point assertion

The source's curve is C: z^2=f(x^2), where

f(t)=(1+sqrt(2))t^3-3(7-3sqrt(2))t^2-3(7+3sqrt(2))t+1-sqrt(2).

Its leading and constant coefficients are nonzero. Direct exact algebra gives disc(f)=442368 and disc(f(x^2))=12524124635136, so the cubic has three distinct nonzero roots and C is a smooth genus-two curve. Choose a root a^2 over C. Then a is nonzero, and P=(a,0), Q=(-a,0) are distinct Weierstrass points. Both quotient maps identify them: the u-quotient coordinates are (x^2,z), while the v-quotient coordinates are (x^2,xz). Both images equal (a^2,0), before or after choosing the displayed identifications of those quotient curves with E1 and E2.

The divisor class [P-Q] is nonzero. Otherwise a rational function with divisor P-Q would give a degree-one map from the genus-two curve to P1. It is a 2-torsion class, since the function (x-a)/(x+a) has divisor 2P-2Q. Thus it is an explicit nonzero element of ker(Phi). This refutes the printed statement that equality of both quotient images forces a=b.

## Exact degree of the displayed homomorphism

Write fu and fv for the u=(x,z)->(-x,z) and v=(x,z)->(-x,-z) quotient maps, in either order. Let

Phi=(fu_*,fv_*): Jac(C) -> Eu x Ev,
Psi=fu^*+fv^*: Eu x Ev -> Jac(C).

Pushforward after pullback is [2] on each elliptic factor. The off-diagonal terms vanish. Indeed u fixes the u-quotient, while on the v-pullback its action is -1: uv is the hyperelliptic involution, whose action on Jac(C) is -1. Therefore fu_* fv^* equals its negative. Hom groups of abelian varieties in characteristic zero have no additive torsion: a homomorphism with finite image from a connected abelian variety is zero. The same applies to the other off-diagonal term. Hence

Phi Psi = diag([2],[2]).

Under the canonical principal polarizations of the Jacobian and elliptic factors, pullback is dual to pushforward. Thus Psi is the polarized dual of Phi, and deg(Psi)=deg(Phi). The composition above is an isogeny. Since both source and target have dimension two, each factor is an isogeny. Multiplication by two on a dimension-two abelian variety has degree 2^4=16. Consequently deg(Phi)^2=16 and deg(Phi)=4. This argument is over characteristic zero, exactly the source's complex setting. It does not replace the source map by a divided or differently normalized map.

## Scope of acceptance and unresolved consequences

This review accepts only the two exact findings above against the frozen contact-worker objection. It does not conclude that Jac(C) cannot be isomorphic to E1 x E2 by a different homomorphism, nor reject the stated integral endomorphism ring or the arithmetic/analytic coordinate theorem. A degree-four isogeny alone does not prove those stronger claims. An additional integral-lattice or independent CM/polarized-moduli argument must be reviewed before calling that a repaired proof.

The source's Proposition 3.8 invokes a similar argument, and Proposition 3.9 cites Propositions 3.7 and 3.8 for its CM calibration. This establishes where the question propagates within the source, not that the conclusions are false. The actual V13 branch/coordinate application and any sufficient repair are assigned to separate non-author reviews. The distinct discriminant-210 literal318 construction is not declared invalid by this discriminant-six finding.

No external issue, author communication, public erratum, or independently accepted repair is asserted. No manuscript, shared proof source, historical decision, or PR has been changed. The publisher PDF and rendered pages are local reading evidence only and are excluded from the public package.
