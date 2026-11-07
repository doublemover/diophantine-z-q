# Actual normal Noetherian proper j-model

This packet strengthens the already constructed actual proper normalization of a finite étale open-j cover. It does not choose or assume normal chart rings independently of that scheme.

- `NormalChart318.sectionsEquiv` identifies the actual normalization sections over the inverse image of an actual open affine chart with the integral closure of its concrete coefficient ring in the concrete cover ring. The comparison uses the exact previously checked section-ring square.
- `NormalJModel318.chart_properties` proves the two actual affine chart rings of the normalization are normal Noetherian domains. It uses the actual finite and reciprocal polynomial coordinates and their proved integral-closure properties.
- The actual inverse-image charts cover the model. `noetherian_model` proves the constructed scheme is Noetherian. `normal_stalk` and `noetherian_stalk` prove normality and Noetherianity at every actual structure-sheaf stalk.
- `NormalJStalk318.codimension_one_dvr` identifies each actual chart-height-one structure-sheaf stalk as a DVR, through its actual prime localization and the previously proved height-one theorem.

Inputs are a nonzero natural level N and an actual domain finite étale algebra B over the literal open-j base. The actual proper target, global normalization, finite map, open dense source inclusion, and source chart comparison are checked predecessor results, not additional inputs.

Still not supplied: the particular modular/PEL algebra/component; regular or semistable resolution; canonical-divisor, Hodge/Arakelov and final global geometric realization. Normality is stated with actual rings and stalks because the pinned library does not package a global normal-scheme class. The codimension-one statement requires the actual chart prime's height to equal one; no full regularity claim is made.

Run `bash build.sh`. All three sources and every introduced declaration are checked with `debug.skipKernelTC=false`; only propext, Classical.choice, and Quot.sound are permitted axiom roots.
