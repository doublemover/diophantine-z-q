# Actual integral modular cover and vertical branch support

## Result and scope

For the actual point-level X_H/Q constructed in `../modular-factor-producer`, with H⊂(Z/NZ)^* and −1∈H, let π=1728/j. For every number field K, the finite normalization of P1_(O_K) in K(X_H) is étale outside the three horizontal sections π=0,1,∞ and vertical fibers above rational primes dividing 6N. In particular **every vertical branch prime divides 6N**. This applies after the arbitrary auxiliary extension used to obtain the semistable resolution and rational chosen fiber.

This note constructs the finite étale open cover and identifies its normalization; it does not infer geometric support from a scalar inequality. `OpenJModel318.lean` additionally constructs the literal Weierstrass model over the actual localized polynomial ring and proves its discriminant is a unit and its j-invariant is the coordinate. The full scheme/torsion/descent/normalization proof below is a classical mathematical application, not a Lean AG formalization. The resolution and finite-divisor intersection argument are supplied by `../finite-divisor-producer-review` and are not repeated here.

## 1. Actual integral elliptic scheme

Assume N>0 and put

    S = Spec Z[j,1/(6N·j·(j−1728))].

This is the same open as Z[1/(6N),j,1/(j(j−1728))]. Define a=−3j/(j−1728), b=−2j/(j−1728). The homogeneous short Weierstrass equation with its section at infinity is

    E: y²z = x³ + a x z² + b z³.

Its literal discriminant and c4 satisfy

    Δ = −16(4a³+27b²) = 1728² j²/(j−1728)³,
    c4 = 144j/(j−1728),       c4³ = jΔ.

Every factor of Δ is a unit on S: 2,3,j and j−1728 are inverted. Hence this is a smooth proper genus-one curve with its section, that is an elliptic scheme over S, and its j-invariant is the actual coordinate j. No field-only nonvanishing argument is being substituted for invertibility in the integral base ring.

The Lean module uses exactly `Localization.Away ((6*N)*X*(X−1728))` over Z[X]. It derives the five units 2,3,N,j,j−1728 from the single inverted product, defines the inverse of j−1728 as a unit inverse, and proves the actual `WeierstrassCurve.IsElliptic` instance and exact `WeierstrassCurve.j` identity, with both preserved under every ring map. It does not merely posit a model with the required invariant.

## 2. Primitive N-torsion is a finite étale scheme

Multiplication [N]:E→E is proper, and its geometric fibers are the finite isogenies of degree N² on elliptic curves in characteristic prime to N. It is therefore proper and quasi-finite, hence finite. It is étale over S. Here is a relative justification rather than applying a field-only assertion without checking its hypotheses.

For a square-zero thickening T0⊂T over S, a lift of a point x0 with [N]x0=y|T0 exists locally because E is smooth. If x is an arbitrary lift, the discrepancy [N]x−y lies in the infinitesimal kernel, canonically Lie(E/S)⊗I. On this kernel [N] is multiplication by N. Since N is invertible, subtracting N^−1 times the discrepancy gives a unique corrected lift. Uniqueness glues the local lifts. Induction handles nilpotent thickenings, proving formal étaleness; finite presentation then gives étaleness. Thus E[N], its base change along the zero section, is finite étale over S.

Étale-locally E[N] is the constant (Z/NZ)²: all geometric fibers have that group structure, and the finite étale isomorphism sheaf of markings supplies a local trivialization. In this trivialization exact order N is a subset of a finite constant set. It is preserved by all transition automorphisms, so it descends to an open-and-closed subscheme T⊂E[N]. Consequently T is finite étale over S. Equivalently one removes the union of E[d] for proper divisors d of N; in the trivialization this is the same open-and-closed condition.

## 3. H quotient without inverting |H|

The constant finite group H acts on T by [h]. This action is free: if [h]P=P and P has exact order N, then N divides h−1, so h=1 in (Z/NZ)^*. The quotient is represented by a finite étale S-scheme Z=T/H. Indeed, after a finite étale local trivialization this is the quotient of a finite set by a finite permutation group; it is a disjoint union of copies of the base indexed by the orbits. These orbit sets and their descent data glue. Equivalently it is the finite coequalizer of H×T⇉T in the finite étale category; this coequalizer is also the scheme quotient and commutes with arbitrary base change.

No averaging, division by |H|, or tameness of H is used. Primes dividing |H| but not6N cause no new branch component in this construction. For example, this includes a characteristic dividing φ(N) while still prime to N. Freeness also shows T→Z is an étale H-torsor, but only Z→S being finite étale is needed for the branch-support conclusion.

## 4. Identifying the chosen rational modular cover, not a twist

On the j-open under consideration, a short Weierstrass elliptic curve with invariant j has both coefficients units, and automorphisms fixing its zero section form μ2. Here is an explicit local isomorphism test. For another short model y²=x³+a'x+b' with the same j and invertible discriminant, j and j−1728 being units imply a',b' are units. Put k=a'/a and l=b'/b. Equality of j-invariants gives k³=l². Étale-locally choose u with u²=l/k; this is an étale quadratic cover because2 and l/k are units. Then u⁴=k and u⁶=l, so scaling x by u² and y by u³ gives the desired isomorphism. The same calculation for automorphisms gives u²=1. This includes arbitrary nonreduced base schemes in the open, using the standard local short Weierstrass presentation after trivializing the Hodge line.

Thus every elliptic curve with the given j is étale-locally isomorphic to E, and any two such identifications differ by ±1. Because −1∈H, this ambiguity acts trivially on the H-orbit of a primitive torsion point. The sheaf Z=T/H therefore is precisely the étale sheaf of isomorphism classes of point-level elliptic curves with an H-orbit of a point of exact order N. This is a coarse/sheaf statement; it does not assert the moduli groupoid has trivial automorphisms or a universal elliptic curve over the coarse quotient.

Over Q this is the open part of the **point-level** X_H used by Mascot (2.1.8), with the same forgetful j-map. It is not the μ_N-model silently substituted via the identity on the upper half-plane. The separate modular-factor producer reconciles those models where needed, but here the explicit point moduli description already matches the actual chosen cover. Since X_H is geometrically connected, this generic cover has one function field Q(X_H).

## 5. Normalization and arbitrary number-ring extension

S is regular, hence normal and integral. The finite étale Z→S is normal. Its characteristic-zero generic fiber is integral; finite flatness excludes any extra component supported only in positive characteristic. Thus Z is connected and integral, and is the normalization of S in Q(X_H). One can apply Stacks tag0BQL directly, or argue affine-locally: its finite normal algebra embeds in its field of fractions, and any element integral over the base is integral over that algebra and therefore belongs to it.

Let K be any number field. Base change gives Z_K^int→S_K^int, where

    S_K^int = Spec O_K[j,1/(6N·j·(j−1728))].

This base is regular: O_K is a Dedekind domain and polynomial rings/localizations preserve regularity. The base-changed cover is finite étale and therefore normal. Its generic fiber is the chosen geometrically connected X_H over K, so the same connectedness/normalization argument applies. Hence Z_K^int is the normalization of S_K^int in K(X_H).

This argument does **not** assert that global normalization commutes with every ramified base change. Instead it constructs the base-changed finite étale model on this open, proves it normal there, and identifies it anew by its generic field. That is exactly what is needed after the auxiliary extension in the semistable-model theorem.

The normalization Y of P1_(O_K) in K(X_H) is finite because the base is excellent/Nagata and the field extension finite. Integral closure commutes with localization, so Y restricted to S_K^int is this Z_K^int. Under π=1728/j the open S_K^int is exactly the complement of π=0,1,∞ after inverting6N; 1728 is already a unit. This proves the claimed horizontal and vertical support.

For emphasis, at a prime ideal of O_K above p∤6N the **generic point** of the vertical P1 fiber belongs to S_K^int: j is then a transcendental residue coordinate, so neither j nor j−1728 vanishes. The normalization map is étale there, hence its local different is zero there. Some closed points of that fiber on the horizontal sections can still lie in the branch locus; they do not give a vertical branch component. The argument makes no unjustified claim of étaleness on the entire good vertical fiber.

## 6. Consumer contract and source check

The output is the actual geometric assertion used in the direct finite-divisor proof:

    vertical branch component of Y→P1_(O_K)
       ⇒ its rational residue characteristic p divides6N.

It is valid over every auxiliary number field and is independent of [K:Q]. It does not bound resolution exceptional terms; the separate negative-definite/Cartier-divisor argument handles those. Resolving Y does not create a new vertical branch component of its original finite normalization map, and no such assertion is needed about the nonfinite composite resolution map.

Fresh standard-source checks:

- Stacks0BFG and0BFH state finite flat degree and étaleness for **abelian varieties over fields**. Their exact scope was checked; the relative multiplication argument above supplies the passage to E/S instead of silently reading them as abelian-scheme theorems.
- Stacks0BL6, Lemma58.5.2 and Remark58.5.3, gives finite étale coequalizers, scheme compatibility and arbitrary base change. This is the precise quotient fact, with no |H|-invertibility requirement.
- Stacks0BQL gives the normalization identification of a connected finite étale cover of a normal integral base.
- Stacks035E recalls localization of integral closure/normalization; Stacks02GH supplies the standard étale and base-change criteria used in the construction.

All six primary HTML pages were freshly read and saved with hashes in `sources/`. The underlying manuscript passage is `quartics/quartic-318-326/docs/arithmetic.md`, anchor `modular-vertical-support`, approximately lines1484–1508. Its argument is accepted with the distinctions just made explicit: field versus relative multiplication, coarse sheaf versus a fine moduli groupoid, and open normality versus unrestricted normalization/base-change commutation.
