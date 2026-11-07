# Actual finite overlap maps, sheaves, and invariant sections

The previously constructed product-localization overlap maps are now proved to be genuine principal localization maps. ProductOverlapOpen318 identifies the actual product localization with the actual iterated localization and proves that the specific existing map intertwines the two algebra structures. It then derives principal-localization, formally étale, and Spec open-immersion properties for both sides. Independence of the coefficient-base presentation of the underlying ring maps is proved, so this applies to the actual source R-algebra maps rather than only abstract S-algebra replacements.

FiniteOverlapSheaves318 applies this to both literal finite Weierstrass Jacobian charts. It constructs genuine O-module differential-sheaf restriction isomorphisms along the actual xMap and yMap. No openness, étaleness, localization-map, or differential-sheaf comparison premise remains supplied for those two maps.

FiniteGlobalFormCompatibility318 transports the actual invariant global differential sections through the genuine canonically normalized sheaf maps, including the exact affine pushforward/global-section identifications. Its final `actual_global_compatibility` is equality of actual global sections of the actual common differential sheaf, derived from the previously checked actual universal differential overlap equality. This is not merely equality of formal coefficients. The preceding canonical-sheaf-comparison identifies these canonical morphisms with the actual restriction isomorphisms.

Remaining work: analogous actual sheaf/open-map binding for the finite/infinity overlap, triple-overlap coherence, and global relative-family differential/Hodge interpretation. The compact modular/PEL base canonical line and arithmetic/analytic source comparison remain distinct. No global source realization or unconditional soundness is claimed.

Run `bash verify.sh`. All three modules are strictly rebuilt; all generated/private declarations are explicitly imported into the standard-axiom audit. Frozen upstream files and repository/Git state are untouched.
