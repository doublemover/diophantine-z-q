# Independent same-field CM surface-height producer

## Result and scope

The argument in quartic_v10.tex, lines7535–7675, is valid with the stated hypotheses: A/L is a CM-type abelian surface, a quaternion division algebra over Q embeds in its geometric endomorphism algebra, every geometric endomorphism is defined over L, [L:Q]≤576, and rad(|D_L|)≤R with R≥1. The conclusion is the original-normalized **surface** height h_F(A)<854R. It is not a bound854R for the rational contact height. A separate metric comparison gives the latter at most1708R+120.

This packet independently verifies the geometric/algebraic source argument below. Its five Lean modules prove the actual fundamental-discriminant/prime-support bound, the actual convergent Dedekind eta product estimate, the finite embedding average, and the exact isogeny-degree logarithmic transfer. It does not define an abelian variety/Faltings-height theory in Lean. The actual period/height identity, isogeny existence and variation, and number-field discriminant-tower identification are explicit remaining geometric producers in the final theorem; they are not replaced with an unproved whole854R assumption.

## Same-field elliptic factor

Over an algebraic closure, A must be isogenous to E² for a CM elliptic curve E. If A were simple, its division endomorphism algebra would act on a four-dimensional rational vector space, so its dimension divides4. Containment of the quaternion division algebra forces equality with it; that algebra has no commutative semisimple subalgebra of dimension4, contrary to CM type. Distinct nonisogenous elliptic factors give a product of commutative fields, again excluding the quaternion algebra. Finally a non-CM repeated elliptic factor would give M₂(Q); an injective map from a four-dimensional division algebra would then be an impossible isomorphism to M₂(Q).

The rational matrix idempotents are defined over L because all geometric endomorphisms are. Images of integral multiples are elliptic subvarieties over L. A homomorphism between the factors extends, using inclusion and a rational projection, to a rational endomorphism of A. Galois invariance of all such endomorphisms shows that the factor isogenies and all endomorphisms of E are defined over L. Thus this argument does not first pass to an uncontrolled splitting field.

Differentiation on the one-dimensional L-vector space Lie(E) embeds F=End⁰(E) into L. A nonzero elliptic endomorphism in characteristic zero is separable and has nonzero differential; after rational scalar extension the map is an injective unital field map. Consequently F is an imaginary quadratic subfield of the same L.

## Same-field maximal order

Write O=End(E). Choose a positive integer f with f O_F⊂O and a Z-basis alpha₁,alpha₂ of O_F. The finite subgroup scheme

    K=(f alpha₁)(E[f])+(f alpha₂)(E[f])

is defined over L, since both displayed endomorphisms and E[f] are. Hence the quotient E'=E/K is over L. In a complex uniformization E=C/Lambda, E[f]=(f⁻¹Lambda)/Lambda, and the displayed subgroup is exactly O_F Lambda/Lambda. The quotient lattice is O_F Lambda, which is stable under the maximal order. Its rational endomorphism field remains F under isogeny; its multiplier order cannot strictly contain O_F. Therefore End(E')=O_F. This gives A'=(E')² and an L-isogeny between A' and A, with no change to [L:Q].

## Fundamental discriminant and ramification

The discriminant tower formula shows that each rational prime dividing the fundamental discriminant D_F divides D_L. Odd primes occur to exponent1 in a quadratic fundamental discriminant; the exponent of2 is at most3. Thus |D_F|≤4 rad(|D_L|)≤4R, including the possible multiplier2³/2=4.

CMDiscriminant318 proves this factor4 directly from Mathlib's Int.IsFundamentalDiscr squarefree characterization and the actual finite prime-factor product. Its retained prime-support premise is exactly the discriminant-tower consequence, not the desired numerical inequality itself.

## Original Silverman normalization

A fresh copy of Barquero-Sanchez et al., Research in Number Theory3(2017), article13, was retrieved from the publisher. Printed page14 was rendered and visually checked. Equation(6.2) is the individual-embedding Silverman discriminant formula. With Delta(z)=(2pi)^12 eta(z)^24, its archimedean summand is

    -log(2pi)-log|eta(z)|²-(1/2)log(Im z).

The paper explicitly uses Silverman's original Faltings normalization. The hypothesis concerning Weierstrass coefficients over Q(j) enters the subsequent class-average argument, not the individual-embedding formula used here. We do not use that class-average assertion.

CM gives potentially good reduction at every finite place. A finite extension with everywhere good reduction is used only to evaluate the stable height; its finite discriminant term vanishes. Its degree is not bounded by576 and is not inserted into the isogeny estimate. The Lean theorem deliberately uses distinct parameters q for the averaging extension degree and d≤576 for the original field.

## Actual eta estimate and averaging

At each embedding choose a reduced period z of fundamental discriminant D_F. Then sqrt3/2≤Im z≤sqrt(|D_F|)/2. Put r=|exp(2pi i z)|<1/16. For every finite partial Euler product, the reverse triangle inequality and 1-x⁻¹≤log x give

    -log|product(1-q^n)| ≤ r/(1-r)².

CMEta318 proves this inequality for the actual infinite product by convergence and its nonvanishing. It then unfolds Mathlib's actual ModularForm.eta to prove

    -log|eta(z)|² < pi Im(z)/6+32/225.

This is not supplied as a premise. The proof includes the convergence/limit and q-parameter norm calculations. To bound the remaining logarithm, the formal proof uses the slightly weaker Im(z)≥1/2, so -(1/2)log Im(z)≤(1/2)log2. Together with pi<4 and the negative -log(2pi), this still proves the stated generous bound on each summand, less than sqrt(|D_F|)+1. Averaging and |D_F|≤4R give h_F(E')<3R, and product additivity gives h_F(A')<6R.

## Isogeny direction, field and degree

The retained original GR Theorem1.9 was independently read and its printed page15 image checked. For a surface its actual parameter is

    Xi(A')=(14^32 d max(1,log d,h_F(A')))^8.

The general part(1), without its separate MM improvement, gives an isogeny A'→A of degree at mostXi(A')². Set the theorem's base field equal to the same L and its optional extension equal to L itself. No CM-to-MM implication is asserted.

The original-normalized half-log isogeny variation gives

    h_F(A)≤h_F(A')+(1/2)log(deg phi).

CMIsogeny318 derives the exact resulting eightfold logarithmic expression from the squared Xi degree bound. Since log14<3, log576<7, log7<2, max(1,log d,h_F(A'))≤7R and log R≤R, it proves h_F(A)<854R. All numeric estimates are kernel checked.

## Source files and remaining formal bridge

The final CMProducer318.original_surface_bound consumes:

- Int.IsFundamentalDiscr D, the actual finite prime support inclusion into nonzero B=|D_L|, and radical(B)≤R;
- actual reduced complex periods with the stated imaginary-part bounds;
- the individual-embedding Silverman equality and product additivity;
- the original-field degree bound, a positive isogeny degree satisfying the actual Xi² expression, and half-log variation.

The classical source argument above supplies these for the actual CM surface under the initial geometric hypotheses. No Lean abelian-variety construction or theorem identification is claimed. Formalizing that global model would be separate work. The whole FiveContact49Height theorem still has other geometric producers and is not concluded by this packet alone.

Primary verification inputs:
- https://doi.org/10.1007/s40993-017-0077-7, publisher PDF SHA2568752beb7b997e31a1f8a5e3ec5a13f5d8c0b675f7862305f1a873cd4b9f5ec8d; page14 image is cm-height-eq62.png.
- metric-cancellation/gaudron-remond-isogenies.pdf and GR-theorem1-9.png, printed page15.
- isogeny-height-transfer/gaudron-remond-2014.pdf, original/shifted convention and isogeny variation, independently checked by the geometric worker.
- diophantine-z-q/manuscripts/quartic_v10.tex, same-field CM lemma lines7535–7675.
