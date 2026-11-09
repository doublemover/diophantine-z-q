# Actual integral noncontact chart and differential frame

Draft only. Hosted strict compilation and distinct source acceptance are pending. No local Lean execution has been run, and the accepted progress snapshot is unchanged.

## Constructed objects

For a commutative coefficient ring R and four actual units c_i, construct the polynomial P(t)=t(t-32)(t-76832)(t+343), the localization R[t,1/P], and the actual tensor product of the four quadratic quotient rings y_i²=c_i(t-a_i). If 2 is a unit in R, the existing quadratic-order theorem proves this finite free order is etale over the localized polynomial ring.

`IntegralContactOpenFrame318.frame` constructs the integral relative Kahler frame by localization and etale base change from the polynomial dt frame. Its value on the actual dt is one. `atPrimeFrame` constructs the same normalized frame in every actual prime localization of this order. No rank-one frame, derivation or smoothness of the order is assumed as an extra input.

`IntegralContactOpenSections318` constructs actual integral cotangent tensors J²/P(t) times dt tensor dt, and t times this tensor, with J=2765952000. It identifies their exact coefficients in the constructed tensor frame. The product-inverse identities prove the denominator is nonzero after every ring map to a field, and the coefficients specialize to the precise rational formulas, not independently chosen scalar values.

## Exact boundary

This construction covers only the integral noncontact open where P(t) is inverted and 2 and the twists are units. It does not cover primes where the arithmetic point reduces to a contact, or coefficient rings in which 2 or a twist is nonunit. It cannot by itself prove the all-finite-place norm bounds. No reduced vertical DVR structure, maximal-stack model, bad-contact chart, global codimension-two extension, PEL identification or KS metric is constructed here.

The construction is over an actual coefficient ring and its actual quotient/localization rings. It is not yet an identification of this integral model with the previously constructed complete rational contact model. The prior actual global sections must still be compared with these tensors through a verified base-change/sheaf map. The exact equations and local formulas agree, but agreement of formulas alone is not asserted to prove that identification.

The source read is `docs/sources/quartic_v10.tex` lines 7015–7037. The prior `ContactKummerOrder318` constructs the rational noncontact cover, while `ContactUnbranchedDifferentialFrame318` constructs its rational dt frame. This packet carries the corresponding actual construction over an integral coefficient ring with the explicitly stated unit conditions. It does not classify the classical model argument as historically absent.

## Application contract

1. Objects. The base is the literal polynomial localization and the cover is the original four-quadratic tensor construction, now over R. The modules are the actual relative Kahler module and its tensor square, not abstract scalar lines.
2. Index coverage. Every coefficient_unit theorem covers all i in Fin 4. All four factors occur in P. atPrimeFrame covers every actual prime of this same open order, without replacing the prime family by a cardinality statement.
3. Domain. P is inverted, and the etale construction requires 2 and all twists to be units. Missing contact and bad-coefficient primes are not claimed covered. Existence of an integral complete-source model is not inferred.
4. Comparison maps. Localization supplies the polynomial-to-base map; the four-root order has its actual base algebra. The R-algebra and its tower are defined explicitly. The dt frame transports through these maps, and atPrimeFrame uses the actual localization at each prime. No additional field identification is asserted.
5. Scalars. All twists remain arbitrary units. Contacts are precisely 0, 32, 76832 and -343. q0 retains J² and q1=t q0. coefficient0_image and coefficient1_image preserve these constants after every field-valued ring map.
6. Consuming objects. The constructed tensorFrame evaluates the actual q0 and q1 tensors to the actual integral coefficients. These are future local inputs to the tensor-image criterion, not yet values of the complete-source global sections at the original arithmetic point.
7. Theorem hypotheses. FourRootOrder318.etale requires unit 2 and all four unit radicands. Unit 2 is transported from R, and each radicand is proved a unit using its twist and the exact inverted contact product. The polynomial frame, localization formal etaleness and etale frame transport then construct the frame. No derivation-preservation assumption is supplied.
8. Historical and downstream scope. The rational construction and source classical metric paragraph are retained. The new prerequisite is an integral open frame and its actual tensors. No manuscript or previous acceptance record is changed, and all-prime integrality remains open.
9. Verification. Source, predecessor and consumer hashes bind the application. Static closure validation does not establish Lean elaboration or semantic identification. Hosted strict compilation, recursive private-inclusive axiom audit and distinct acceptance remain pending; no self-approval is supplied.
