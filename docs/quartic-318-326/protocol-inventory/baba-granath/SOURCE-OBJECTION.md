# Baba–Granath: displayed quotient-map objection

Date: 2026-11-08. Author: model worker /root/restart_contact_field. This is a new objection and derivation awaiting non-author review, not an acceptance of a repair. No manuscript or shared proof files changed.

## Exact source

S. Baba and H. Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, DOI https://doi.org/10.4153/CJM-2008-033-7. Final publisher PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/E6B7F5233E98E9C8E013658575FF713F/S0008414X00022008a.pdf/genus-2-curves-with-quaternionic-multiplication.pdf . SHA-256 c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c. Printed p.743, Proposition 3.7 and proof; p.744, Propositions 3.8–3.9. These pages were read from text and rendered images. The cited March 17, 2005 preprint (SHA b049ce64f9b662af0e078f4faa9e5325cc7a99bf2d6ccda0a31a84719d031c32) contains the same argument in Proposition 8, followed by Propositions 9–10.

## The exact map, not a different abstract isomorphism

The source takes the smooth genus-2 curve C: z²=f(x²), and the complementary involutions u(x,z)=(-x,z), v(x,z)=(-x,-z). Their degree-two elliptic quotient maps are f1 and f2, after ordering targets E1,E2. It constructs Φ=(f1_*,f2_*): Jac(C)→E1×E2 and infers that Φ is an isomorphism from the absence of a pair of distinct curve points having both quotient images equal. The claimed conclusion for this displayed homomorphism does not follow.

Let Ψ=f1^*+f2^*: E1×E2→Jac(C). The diagonal terms f_i,* f_i^* are [2]. The off-diagonal terms vanish: u acts by +1 on one pulled-back elliptic factor and -1 on the other, since v is u composed with the hyperelliptic involution, which acts by -1 on Jac(C). Thus each off-diagonal Hom map is its own negative; Hom between abelian varieties in characteristic zero has no additive torsion, so it is zero. Consequently ΦΨ=diag([2],[2]). Under the canonical principal polarizations, Ψ is the transpose/dual of Φ. The composition is an isogeny, hence both factors are isogenies; their degrees are equal. Therefore (deg Φ)²=deg([2] on E1×E2)=16, and deg Φ=4, not 1.

There is an even more direct reason the curve-point test fails: take a Weierstrass point (a,0) with a≠0 and its partner (-a,0). Both quotient maps identify that pair, since f1 uses (x²,z) and f2 uses (x²,xz). Such points exist on this sextic because f has three distinct nonzero roots. Thus the asserted injectivity of the pair on C is also false. Their difference is a nonzero Jacobian 2-torsion element in the kernel. This observation is over the algebraic closure and does not depend on rationality of the Weierstrass points.

This does NOT disprove the separate abstract statement that Jac(C) might be isomorphic, as an unpolarized abelian variety, to E1×E2 by some other map. Nor does it by itself disprove the stated center/endormorphism ring, the j-coordinate theorem, or the downstream height theorem.

## Precise downstream exposure and sufficiency boundary

Published Proposition 3.9 fixes the arithmetic/analytic coordinate equality j=j_m², citing Proposition 3.7 for the -24 CM value and Proposition 3.8 for the -19 value and its orientation test. Proposition 3.8 explicitly invokes the analogous argument. The numerical Igusa values -16/27 and 81/64 are separate algebraic computations; the missing step is not merely their substitution, but identification with the indicated optimal CM points of the same polarized quaternionic model.

The degree-four isogeny does prove the rational CM-center statement: if E1,E2 have CM by K and are isogenous, Jac(C) is isogenous to their product and has rational endomorphism algebra M2(K). This is weaker than the asserted integral maximal endomorphism ring and than the exact optimal-order/polarization identification used to locate the CM points. A proof that this weaker information suffices, or a separate correct integral/CM identification, remains to be supplied and independently reviewed. No replacement proof is claimed here.

V13 SHA-256 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd consumes the branch-value identification at lines 487–498, then the pullback ramification at 586–598 and the polarized-moduli coordinate at 608–618. This is the discriminant-6 six-contact route. The distinct discriminant-210 five-contact construction at 6868–6943 starts from González–Rotger quotients instead; no implication about its own PEL/Jacobian identification follows from this objection alone.

## Historical and current status

The historical repository geometry report checked the preprint's source interface and correctly distinguished its polarization convention. Its declared read scope does not include a derivation of the map-degree claim on preprint pp.10–11. I found no earlier resolution of this specific objection in the geometry report or associated application records. This is a bounded search, not a claim of exhaustive historical absence.

Targeted web searches and the publisher record did not identify an applicable erratum. That is not proof that no correction exists. The final published source is available and the preprint limitation can be removed at the bibliographic level, but this newly identified proof objection must remain recorded pending disposition. No theorem-false verdict, silent repair, or full application acceptance is made.
