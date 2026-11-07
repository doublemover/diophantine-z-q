# Actual height-one stalks, completions, and contact normalization

This packet has three strictly kernel-checked modules and 21 exhaustively audited declarations. The only axioms occurring recursively are `propext`, `Classical.choice`, and `Quot.sound`.

## Proved objects and maps

- `HeightOneDVR318.localization` proves that the actual localization of a normal Noetherian domain at an actual prime ideal of height one is a discrete valuation ring. Its DVR structure is derived from normality, Noetherianity, the localization dimension theorem, and the Dedekind-domain characterization. No regular-local or DVR premise is supplied.
- `AffineHeightOneStalk318` uses the actual Mathlib scheme `Spec R`, its actual presheaf stalk, and its canonical stalk/localization isomorphism. It installs the structure sheaf's canonical coefficient algebra, with `coefficient_germ` identifying its map with the actual germ. The stalk's DVR structure, its actual adic completion's DVR structure, faithful flatness, and exact canonical valuation preservation follow.
- `HeightOneContact318.source_formal_map` composes the actual source coefficient algebra, canonical germ, and actual completion. For a uniformizer and a positive even contact order it constructs the genuine formal-series map with the specified parameter and constant coefficients. There is no supplied formal base map or convergence premise. Positive order is essential: arbitrary formal evaluation at a unit is not claimed.
- `source_local_normalization` constructs the actual finite etale normalization of the even quadratic contact order over that actual stalk. It derives the integral closure statement, finite/etale properties, injection into the actual generic fiber, and generic-fiber algebra isomorphism, using the previously checked contact and etale-normalization packets. The possibly split quadratic algebra is not called a field.

## Exact retained boundary

The input ring must actually be a normal Noetherian domain, and the point must actually have height one. This packet does not assert the existence of the global contact/modular model, identify a geometric branch cover with the quadratic contact order, produce its local parameter or even contact valuation, or prove global resolution, adjunction, intersection, or Arakelov identities. Those are distinct geometric realization steps. It does not prove `GeometricRealization`, `FiveContact49Height`, or unconditional end-to-end soundness/completeness.

## Reproduction

Run `bash run.sh`. It strictly rebuilds all three sources and then audits every declaration belonging to those three modules, including generated instances and proof helpers. The script uses the existing pinned Lean/Mathlib project and sibling frozen dependency packets. The source and build-log hashes are bound in `receipt.json` and `SHA256SUMS`. Generated `.olean` objects are not deliverables.
