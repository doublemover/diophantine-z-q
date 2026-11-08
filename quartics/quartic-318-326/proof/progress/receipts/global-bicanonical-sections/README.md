# Global intrinsic bicanonical sections

This packet constructs two genuine global sections q0 and q1 of the actual
intrinsic cotangent tensor-square sheaf on the complete contact normalization,
for every choice of nonzero rational twists c_i. It proves their exact local
restrictions on the actual five-chart cover.

## Actual objects and formulas

`ContactGlobalBicanonical318.tensor_eq` identifies the tensor object by reflexive
equality with `ContactBicanonicalSheaf318.bicanonical`. The global sections are
`ContactGlobalBicanonical318.q0` and `.q1`; `.q0_restrict` and `.q1_restrict`
retain their local universal-coordinate expressions.

The direct sections use coefficient times the genuine pure tensor of the
universal coordinate differential with itself. On branch i this is Dz_i
squared, with q0 coefficient 4*C_i/(c_i*D_i) and q1 coefficient t times that.
At infinity the coordinate is u=c_0/y_0, and the coefficients are
4*C_0*u^2/(c_0^5*D_inf) and 4*C_0/(c_0^4*D_inf), respectively.

The construction deliberately uses these direct universal-coordinate sections
rather than the previous inverse-frame local section names. Their underlying
sheaf is exactly the same, and their coefficients are unchanged. The prior
normalization packet verifies the frame/differential normalization; a redundant
concrete alias-composition draft encountered kernel elaboration blowup and is
not included. This packet does not assert a new theorem equating the two sets
of local section names.

## Proof joins

1. On each entire branch ring, P(t)*q0_i equals the square of the actual
   differential coefficient in Dt=(2*z_i/c_i) Dz_i. The branch point itself
   is retained; only the other three contact factors have been inverted.
2. Each branch and infinity map is the checked Q-algebra map into the same
   whole unbranched OpenOrder. P(t) is an actual unit there. The infinity
   denominator identity retains c_0^7 and u^8. Differentiating u^2*t=c_0 and
   cancelling the actual unit u yields the exact infinity differential factor.
3. These equations imply equality of the weighted pure tensors as actual
   intrinsic tensor sections on the common open. The q1 equation follows from
   q1=t*q0 there, including the actual infinity coefficient.
4. The generic tensor restriction theorem transports the actual coefficient
   and both universal differential factors along the specified affine map.
   The checked Scheme map squares identify these restrictions with the same
   original common chart. Exact image equalities supply every complete
   branch/infinity and distinct finite/finite intersection. No dense-open
   extension principle is substituted.
5. The verified five-chart cover and literal full-intersection compatibility
   feed the actual sheaf gluing theorem, giving global q0 and q1 with the
   stated exact local restrictions.

## Scope retained

No linear-independence or base-point-free theorem is claimed yet. Nor are a
projective map from these sections, its degree, a genus/canonical-degree result,
a choice of twists from the Shimura source, or a PEL/Kodaira-Spencer comparison
claimed. The source is the actual checked complete contact normalization for
the chosen arbitrary rational units.

## Validation

The twelve sources are compiled strictly in MODULE_ORDER.txt order. The joined
recursive audit includes these sources, the thirteen contact/tensor foundation
modules, the ten normalization modules, and the thirteen overlap/denominator
modules. It permits only propext, Classical.choice and Quot.sound. Compiler
results, exact sources, predecessor receipts and dependency bindings are in
receipt.json. This is a bounded packet replay, not a clean whole-repository
rebuild. Failed and redundant exploratory drafts are excluded.
