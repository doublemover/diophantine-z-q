# The displayed Baba–Granath map has degree four

This note concerns one specified map, not the possibility of another isomorphism between the same abelian varieties. It gives a concrete counterexample to the injectivity assertion and computes the entire geometric kernel.

## Source and claim

S. Baba and H. Granath, *Genus 2 Curves with Quaternionic Multiplication*, Canadian Journal of Mathematics 60(4) (2008), 734–757, Proposition 3.7 and its proof, printed p.743 (PDF p.10). DOI: https://doi.org/10.4153/CJM-2008-033-7 . The final publisher PDF has SHA-256 c711b2bed2aa0dd70d1bc1dd06c6d4a921c4b8735452bc143431f080a8cac12c. The following page invokes a similar argument for Proposition 3.8 and uses the resulting CM identifications in Proposition 3.9.

In Proposition 3.7, C is the smooth genus-two curve z²=f(x²), where

f(t)=(1+√2)t³−3(7−3√2)t²−3(7+3√2)t+(1−√2).

The two involutions are u(x,z)=(−x,z) and v(x,z)=(−x,−z). Their quotient curves have equations s²=f(t) and s²=t f(t), respectively, with quotient coordinates (t,s)=(x²,z) and (x²,xz). After choosing elliptic origins, write their maps as f1:C→E1 and f2:C→E2. Translating an origin does not change the induced map on Pic⁰.

The map at issue is

Φ=(f1,*,f2,*):Jac(C)→E1×E2,

where f_i,* is the norm/pushforward map on degree-zero divisor classes. The source concludes that this map is an isomorphism after asserting injectivity of the pair of quotient maps on curve points. Both assertions about these displayed maps fail.

## A direct counterexample to point injectivity

The cubic f has three distinct nonzero roots r1,r2,r3. This can be checked directly: its constant and leading coefficients are nonzero and its discriminant is 442368. Choose square roots ai of ri. The six points Wi⁺=(ai,0) and Wi⁻=(−ai,0) are distinct Weierstrass points of C over C.

For each i, both quotient maps identify Wi⁺ and Wi⁻:

(x²,z)=(ri,0), and (x²,xz)=(ri,0).

Thus the source's assertion of injectivity of the pair on C is directly contradicted by these actual points. Their images under the two quotient maps are well-defined affine points because ai≠0.

The divisor class Di=[Wi⁺−Wi⁻] is nonzero. If it were principal, a function with divisor Wi⁺−Wi⁻ would give a degree-one map from a genus-two curve to P¹, which is impossible. Also 2Di=0 because (x−ai)/(x+ai) has divisor 2Wi⁺−2Wi⁻. Therefore Φ already has a nonzero two-torsion kernel element.

## Computing the degree exactly

Let J=Jac(C), and let

Ψ=f1*+f2*:E1×E2→J,

where f_i* denotes pullback on Pic⁰. Each quotient map has degree two, so f_i,* f_i*=[2]. Under the canonical principal polarizations of J and E1×E2, Ψ is the transpose of Φ.

The off-diagonal compositions vanish. For example, u acts trivially on f1*(E1). The product uv is the hyperelliptic involution, which acts as −1 on J, while v acts trivially on f2*(E2). Hence u acts as −1 on f2*(E2). As f1,*u=f1,*, it follows that f1,*f2*=−f1,*f2*. A homomorphism between complex abelian varieties annihilated by two has connected image contained in a finite two-torsion group, so it is zero. The other off-diagonal composition is zero in the same way.

Consequently

ΦΨ=diag([2]E1,[2]E2)=[2]E1×E2.

This is an isogeny. Since both the source and target of Φ and Ψ have dimension two, Φ and Ψ are themselves isogenies. A map and its transpose under principal polarizations have the same degree. Multiplicativity of degree therefore gives

(deg Φ)²=deg([2]E1×E2)=2⁴=16,

so **deg Φ=4**, not one.

All maps here are over characteristic zero, so the kernel is reduced and has four geometric points. In fact it is exactly {0,D1,D2,D3}. To check the relation, choose the square roots ai and consider

z / ((x+a1)(x+a2)(x+a3)).

Its divisor is Σi Wi⁺−Σi Wi⁻; the orders at the two points at infinity cancel. Thus D1+D2+D3=0. The Di are all nonzero, and this relation shows they are pairwise distinct. They lie in ker Φ, so they give all four kernel points. In particular ker Φ≅(Z/2Z)².

The same computation applies to the complementary degree-two quotients in Proposition 3.8. Its cubic has distinct nonzero roots as well; the companion exact arithmetic receipt verifies this independently.

## What this proves, and what it does not

It proves that the particular quotient-induced map in the published proof is a degree-four isogeny and that its stated curve-point injectivity argument is false. It does **not** prove that Jac(C) and E1×E2 cannot be isomorphic by some other map. It also does not identify the Jacobian polarization with a product polarization. The separately authored REPAIR.md explains a possible correction recovering the abstract unpolarized product using the actual maximal quaternionic action and integral lattices; that correction requires its own independent review.

The exposed manuscript dependency is the discriminant-six, six-contact route: V13 uses Baba–Granath's normalized polarized j-coordinate and branch labels. Proposition 3.9 consumes the CM identifications whose original proof used this map. The invalid displayed-map argument must therefore be recorded and either repaired or replaced; simply repeating the citation does not settle it.

The current literal 318/326 height49/8 route instead uses discriminant 210 and the González–Rotger quotient construction. This displayed D6 map is not its premise. The PP/RC completeness route also does not use a height theorem. These nondependencies do not declare the separate D210 geometric/formal obligations complete. Exact downstream source bindings accompany this note and the distinct dependency review.

Authorship: /root/restart_group_law, 2026-11-08. Contact identified the original objection; geometric independently confirmed the map degree. This note supplies an explicit full-kernel presentation and does not stand in for its own non-author review. No external party has been contacted and no manuscript has been changed.
