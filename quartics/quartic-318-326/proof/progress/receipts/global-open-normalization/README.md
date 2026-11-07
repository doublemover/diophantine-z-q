# Actual global open normalization and proper extension

Two modules, eight public theorems, nine recursively audited declarations. Fresh strict kernel replay passes with only propext, Classical.choice and Quot.sound.

`GlobalOpenNormalization318` derives local quasi-finiteness and local finite type from actual finite source section algebras over denominator-localized target rings. The affine restriction is the genuine scheme restriction and its ring map is transported by the actual restriction arrow isomorphism. The resulting `toNormalization_open` invokes Mathlib's proved Zariski main theorem to prove that the actual source-to-normalization morphism is an open immersion.

`GlobalCompactification318.affine_of_cover` derives actual affineness from affine inverse images on an actual target cover. `open_finite_factorization` combines the open immersion with the previously checked actual finite global normalization. The exact composite is the original scheme map. `proper_extension` composes with an actual proper target map, giving an actual proper extension of the source, not a family of unrelated affine models.

## Scope

The input is a genuine scheme morphism and genuine covering by target affine opens, with its actual source inverse-image section rings, localization rings and compatible scalar towers. Finite smooth domain algebras over the denominator opens yield the finite normalization; local quasi-finiteness and finite type themselves do not require smoothness or domains. The target section rings in the final finite/proper result are normal Noetherian characteristic-zero domains, and denominators are nonzero. Actual properness of the target remains explicit.

This constructs the relative normalization and open/finite/proper factorization. It does not instantiate the specific modular/PEL source cover, construct a proper projective j-line target, assert a regular or semistable resolution, or prove GeometricRealization/FiveContact49Height. Those source-object and model identifications remain separate.

The unchanged official Mathlib `ZariskisMainTheorem.lean` dependency was itself rebuilt with strict kernel checking; its source hash and replay log are recorded. All delivered source modules are listed in the receipt. Diagnostic Check.lean and temporary logs are not deliverables.
