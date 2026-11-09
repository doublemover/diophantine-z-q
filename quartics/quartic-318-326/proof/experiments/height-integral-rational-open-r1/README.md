# Identify the integral chart's rational specialization

Draft only. No local Lean execution. Hosted strict checking and independent acceptance are pending. Two predecessor modules are copied byte-for-byte from `height-integral-contact-chart-r1`, which is still an unaccepted prerequisite.

`IntegralRationalOpenComparison318` identifies the new integral-chart construction specialized to R=Q with the existing original `ContactKummerOrder318.OpenOrder c`. It proves equality of every literal contact, coefficient polynomial, and denominator; constructs an actual ring equivalence; and proves that equivalence preserves the original t-coordinate, inverted contact product, inverse product, and both J²-scaled section coefficients. The equivalence is promoted to a rational algebra equivalence. Its actual relative differential map sends the new dt to the original dt.

This establishes object identity on that rational noncontact chart, not merely agreement of displayed equations. It does not establish that rational specialization is the tensor-product generic fiber of an arbitrary integral coefficient ring, construct bad-contact charts, or identify the new integral tensors with restrictions of the complete-source global sheaf sections. The latter comparison still needs the actual tensor/sheaf pullback along this equivalence and the existing original chart embedding. All-finite-place metric inequalities, PEL geometry and KS remain open.

Source context read: `docs/sources/quartic_v10.tex` lines 7015–7037. Existing original chart/frame producers read: `ContactKummerOrder318` and `ContactUnbranchedDifferentialFrame318`. The new comparison preserves their exact rational twists and all four labels.

## Application contract

1. Objects. The comparison source is the actual polynomial-localization/four-root order from the integral-chart packet at R=Q. Its target is the original ContactKummerOrder318.OpenOrder with its original coefficient and ring structures, not a newly selected curve.
2. Indices. contact_eq and coefficient_eq quantify over every i in Fin 4; denominator_eq covers their complete product. No contact label or twist is silently identified or dropped.
3. Domain. Both sides are the same rational noncontact open. This does not cover the complete curve, infinity or integral contact-reduction primes, nor establish general integral-to-rational tensor base change.
4. Maps. The constructed ring equivalence maps the new coordinate, product and inverse into the exact original ones. Its rational-algebra promotion uses uniqueness of the rational scalar homomorphism. The resulting relative differential map has the correct direction from source differentials to target differentials and preserves dt.
5. Scalars. Contacts are 0, 32, 76832, -343 with arbitrary original rational unit twists. The coefficient identities retain J² for J=2765952000, and the second coefficient remains t times the first. No factor 32 or field extension is absorbed.
6. Consumer. The original rational open order and its actual universal differential are the targets. The theorem supplies the coordinate/coefficient/differential identification needed for a later actual tensor/sheaf comparison; that next comparison is not asserted here.
7. Hypotheses. The ring comparison uses proved polynomial and denominator equalities, not an assumed isomorphism. Algebra-map and differential compatibility use their actual functorial theorems. All integral-chart hypotheses remain exactly those of its copied producers.
8. History. The original rational open and rational dt frame were already constructed. This draft is a formal comparison with the new integral-chart presentation, not a newly claimed historical geometric construction. The manuscript and accepted snapshot remain unchanged.
9. Verification. The copied predecessor bytes, source imports, consumer sources and all three packet modules are hash-bound. Static checks do not certify Lean elaboration. Hosted strict compilation, recursive private-inclusive axiom audit and distinct source acceptance remain pending.
