# Actual reciprocal open-j algebra and normalization

Fresh strict replay passes 54 recursively audited declarations in three modules; only propext, Classical.choice and Quot.sound occur.

The ordinary base is the literal Z[j,1/(6N*j*(j−1728))]. The reciprocal base is the actual localization Z[s,1/(6N*s*(1−1728s))]. `ReciprocalJ318.reciprocalEquiv` constructs an actual ring isomorphism in both directions and proves its inverse laws, with j sent to s⁻¹ and s to j⁻¹. Denominator units are proved in the actual localized rings, not assumed from a rational-function substitution.

For an actual finite etale open-j algebra B, `ReciprocalCover318` constructs its actual reciprocal cover map, proves finite/etale properties by the constructed isomorphism, and uses the exact polynomial scalar map to derive a finite normal Noetherian second-chart integral closure. This map sends s to the image of the actual inverse j-unit. The nonzero N hypothesis is used exactly to make the reciprocal polynomial denominator nonzero for the finite-normal-model theorem; the base-ring isomorphism itself does not need it.

`ReciprocalProjective318.coverMap_infinity` proves that the actual source Scheme map to the actual proper projective j-line factors through precisely this reciprocal polynomial map. Thus the second finite normal affine model is bound to the real projective source map, not a separately chosen function-field coordinate.

Remaining work: transport these two concrete affine normalization results into the actual global normalization's section-ring chart interfaces, then conclude properness of that actual global normalization. The source modular/primitive-torsion cover/component, regular/semistable resolution and arithmetic/PEL realization remain external. No unconditional GeometricRealization or FiveContact49Height is claimed.
