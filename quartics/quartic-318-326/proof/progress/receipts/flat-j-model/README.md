# Proper flat arithmetic j-model

The actual structure morphism of the already constructed proper normal j-model is proved flat, surjective and locally of finite presentation over Spec Z. These properties refer to the same scheme and the same Z-morphism as the preceding proper-normalization packet.

`FlatJChart318.cover_charZero` derives characteristic zero of the actual finite étale domain algebra from flatness over the nonzero denominator localization of Z[j]. Its actual normal model chart rings map to that algebra through the proved integral-closure/section-ring comparison, so their characteristic zero is derived too. A characteristic-zero domain is torsion-free, hence flat, over Z. The actual affine cover and its restriction/global-section isomorphisms then prove `model_flat`.

`ArithmeticJModel318.model_dominant` proves the original characteristic-zero source has dense image in Spec Z and uses the exact dense-open model factorization. Actual properness closes the image, giving surjectivity. The proper morphism has locally finite presentation over the Noetherian target. `proper_flat_surjective` packages only these derived properties, with no model/flatness/characteristic-zero/surjectivity premises.

Inputs remain a nonzero level and an actual domain finite étale algebra over the literal open-j base. The particular modular/PEL algebra or component, its regular/semistable resolution, and the Arakelov/geometric realization are still not constructed here. No smoothness, regularity or fiber-dimension assertion is inferred from flatness alone.

Rebuild with `bash build.sh`. Both modules and all declarations are recursively audited under strict kernel checking. Only propext, Classical.choice and Quot.sound are permitted.
