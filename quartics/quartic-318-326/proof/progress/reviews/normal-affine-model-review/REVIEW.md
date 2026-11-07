# Independent review: genuine normal affine model

Accepted. All four source modules and the exhaustive audit were copied without changes, then rebuilt in the review directory with `-Ddebug.skipKernelTC=false`. All 25 declarations pass with only propext, Classical.choice and Quot.sound.

The generic fiber is the actual tensor product B tensor_R K. The domain hypothesis is explicitly on B, not inferred from an arbitrary finite étale algebra. Smoothness supplies flatness, and the nontrivial domain case supplies the needed faithful embedding. Localization and finite-dimensionality then construct a genuine field structure. The fraction-ring proof checks denominators and injectivity rather than assuming that field is the function field.

Normality of the open algebra is derived from the already reviewed smooth integral-closure theorem. The full integral closure over the original normal Noetherian base is identified inside this actual field. Finiteness uses the finite separable fraction-field extension and the integral-closure finiteness theorem. In the final source-shaped application, separability follows in characteristic zero. Normality and Noetherianity of the entire integral closure, not just a finite order, are proved.

The literal open-j specialization uses Z[X] localized away from 6*N*X*(X-1728), with N nonzero explicitly. Its source B must be a genuine domain finite étale algebra over that actual base. The scheme morphism is the genuine affine Spec structure map. Its finite and proper properties are over the affine integral j-line: this is not a projective compactification or a proper arithmetic curve over Z.

No source connected-component/PEL-family construction, compactification, regular-model construction, or Arakelov realization is claimed. These boundaries agree with the producer receipt. No semantic mismatch found.
