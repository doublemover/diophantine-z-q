# Injective normalization and literal-generator independence

Status: source-policy and dependency-closure checks passed; hosted Lean and distinct review pending. No local Lean compilation was run. The packet has four sources: two unchanged radical/point-sign producers and two new consumers. It is an algebraic result, not a real-density or component-modulus theorem.

## Actual additive normalization

NormalizationInjection318 constructs the literal coefficient curve E_d: y^2 = x^3-d*x. It proves its discriminant is 64*d^3, so nonzero d gives ellipticity. The curve is already in short normal form.

For any field embedding phi:F->L, r nonzero, and phi(D)=r^4, normalize is the composition of:

1. ShortCurveBaseChange318.pointMap, from the actual E_D group to E_phi(D).
2. Exact coefficient transport along phi(D)=r^4.
3. ShortScaling318.pointAddEquiv with the unit r^-1, from E_(r^4) to E_1.

The a4 condition is -1=(r^-1)^4*(-r^4) and the a6 condition is 0=(r^-1)^6*0. Both source and target ellipticity are established before applying the original scaling theorem. Base change is injective, and both subsequent maps are additive equivalences, so the whole normalization is an injective additive map on every nonsingular point, including infinity.

The source-to-target reciprocal formula is proved: point(D,u,v) maps to point(1,r*phi(u),phi(v)). The u=0 case is retained separately, and the finite case has x scaled by r^-2 and y by r^-3. Nontorsion therefore transports from the original point, rather than being assumed anew on a related normalized point.

The concrete first and second image lemmas identify these maps with the exact firstPoint and secondPoint of the copied sign producer. They retain the original source D and deltaBar^2 respectively.

## The literal source generator, with no nontorsion hypothesis

NormalizedGeneratorIndependence318 defines firstGenerator by normalizing LocalGenerator318.P with base and firstRoot. It defines secondGenerator by normalizing that identical P with base composed with SourceContact318.conj and secondRoot. The exact identity conj(D)=deltaBar^2 establishes the second coefficient condition. These are concrete algebraic points over the actual four-dimensional root field Both.

Both nontorsion statements now follow from GeneratorMultiplesTwo318.generator_infinite_order, carried through the proved injective additive normalizations. The unchanged source theorem uses exact 2-adic valuations of the actual P multiples. No new rank, density, nonzero-coordinate or infinite-order premise is inserted.

The selective field involution induces the already constructed additive flipPoint on E_1. Applying it to the actual normalized finite coordinates fixes firstGenerator and negates secondGenerator: it fixes the K-coefficients, fixes firstRoot, and negates secondRoot, so the reciprocal x coordinate is unchanged while the second y coordinate is negated. Point.neg_some is the actual group-negation formula.

The final integer_relation theorem says that m*firstGenerator+n*secondGenerator=0 implies m=n=0 for all integers m,n, with no additional assumptions. It applies the previously proved selective-sign argument using these specific proved nontorsion and sign statements. No identity of the source generator with an arbitrary chart point is required for this endpoint: both actual definitions take the literal P itself.

## What this does not establish

The packet does not construct the chosen real embedding of Both or show that its root signs match a particular real normalization. Nor does it compare these algebraic target points with the actual real oval orbit used by the mixed-CRT packet. The original quartic-to-reciprocal elliptic map and possible finite kernel need their precise real-group comparison. A valid circle/character or compact-Lie argument is still needed to derive any real orbit-closure statement from algebraic integer independence. The concrete return modulus and the scalar/guard-good intersection with the actual identity component remain open.

These are scope boundaries, not claims of newly discovered historical gaps. The historical compact-Lie/component argument in quartics/quartic-318-326/docs/arithmetic.md and docs/sources/quartic_v10.tex, lines10632-10694, retains prior-justification-found status. No accepted manuscript or baseline is changed. The first51 rows, remaining237 rows, mixed-CRT arithmetic inputs, root signs, scalar threshold, and final source polynomial are unchanged.

## Validation and source identity

SOURCE-COPIES.json binds both unchanged producers. DEPENDENCY-PINS.json binds all44 required baseline modules, including the exact original scaling, base-change, conjugation and source-generator nontorsion producers. The source checker rejects placeholders and unknown/nonpreceding imports; it is not a Lean elaborator or independent mathematical review. A recursive axiom audit is prepared for hosted CI. No browser tabs were opened.
