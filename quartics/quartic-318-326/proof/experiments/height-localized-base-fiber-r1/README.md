# Localizing the actual reduced base fiber

Draft only. Hosted kernel checking and independent acceptance are pending. No local Lean compilation was run, and the accepted progress snapshot is unchanged.

This packet copies all six sources of `height-ramified-base-sections-r1` unchanged and adds two bridge modules. `LocalizedReducedFiber318` proves that a reduced quotient A/I remains reduced after actual localization A to B: radicality is transported through the same ideal map. It then computes the mapped principal ideal and identifies the image of the same base parameter r through the actual R to A to B scalar tower. `LocalizedBaseTensorSections318.integral_sections` feeds exactly that resulting reduced B/(r) into the existing ramified-base tensor-integrality theorem.

Thus a single reduced whole affine fiber A/(r) supplies the needed reduced local fiber at every actual localization, including prime localizations. The DVR condition, an actual integral relative differential frame at B, and the nonzero/nonunit image of r remain explicit inputs. Neither the affine reduced special fiber nor the semistable model is constructed here. In particular, the good-chart packet's field fibers over a punctured affine line are not confused with the whole arithmetic special fiber A/(r), and are not used to discharge this input.

The four original contacts, literal J = 2765952000, its square scaling, generic coordinate, actual relative derivation, and tensor inclusion are retained. A ramified base uniformizer is not replaced by a rational prime. The map from the integral tensor module is the original map tied to the actual differential map on pure tensors. The local geometric prerequisites and complete place coverage remain open.

## Application obligations

1. Objects: actual rings R, A, B, generic field K, actual localization M of A at B, and actual quotient by the image of one r in R. The conclusion is an integral tensor preimage for each original generic q0 and q1.
2. Indices: the reduced quotient localization theorem covers any submonoid M and hence every prime localization. Existing valuation bounds still use all four original contacts, with no prime or contact omitted from their stated domain.
3. Domain: a reduced whole affine quotient A/(algebraMap R A r) is assumed. B must genuinely be its specified localization and a DVR, the base parameter is nonzero and nonunit there, and the differential frame is actual. These conditions are not inferred from the finite etale arithmetic point cover.
4. Coefficients: the same base parameter r is transported through the original scalar tower. J-squared and original contact constants are unchanged, and no normalization of the rational prime's valuation is imposed.
5. Local conditions: reducedness of the local quotient is constructed by radical ideal localization; only whole affine reducedness is assumed. DVR and frame existence remain explicit geometric inputs, not fabricated consequences.
6. Transition maps: Ideal.map uses algebraMap A B; the principal ideal is computed as span of the actual mapped parameter. Scalar tower compatibility identifies that parameter with algebraMap R B r. The tensor map remains IntegralCotangentTensor318.map for the actual local frame.
7. Identity: the reduced quotient is precisely the quotient consumed by ReducedBaseTensorSections318; it is not an unrelated residue algebra. The resulting generic tensors are precisely VerticalCotangentSections318.q0 and q1 at the same t.
8. Consumers: this replaces a local reducedness hypothesis with a whole affine reducedness hypothesis plus verified localization. It does not claim construction of a global model or complete integral section realization, and leaves preceding pending experiments unchanged.
9. Validation: unchanged predecessor hashes, source and consumer pins, primary upstream ideal-localization statements, and static import/hash checks are recorded. Hosted kernel/audit and independent acceptance are pending. Structural audit self-tests are not proof acceptance.
