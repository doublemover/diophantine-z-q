# Independent global-energy-to-cusp constructor review

PASS. Exact copies of `GlobalCuspEnergy318` and `GlobalEnergyJacobian318` were rebuilt with `debug.skipKernelTC=false`. The exhaustive recursive audit passed 41 declarations across two modules, permitting only propext, Classical.choice and Quot.sound. Source equality and dependency receipt hashes are recorded below.

The Data constructor does not accept the local area-energy or integrability bounds it claims to derive. It takes actual nonnegative global measures, mass at most one, an almost-everywhere measurable coordinate, and the exact pushforward/restricted-density equation. Holomorphic coefficient functions supply measurability. The imported normalized-chart-energy theorem then proves actual local integrability and the real area integral bound, so the totalized Bochner integral at a nonintegrable function is not being used to fabricate an estimate.

For every actual complex embedding and every differential, `toCusp` preserves the identical coefficient functions, q-parameters, widths, non-Weierstrass condition and G data. Only the integrability and energy fields are constructed. It does not change the averaging convention or choose a different chart for the differential and Wronskian. Exact density transport contains the coordinate measure and excludes an unaccounted covering multiplicity; no additional factor two belongs in ordinary area.

The second module applies the already frozen finite/Arakelov wrapper to precisely `D.toCusp`. Its named Arakelov identities reference that same constructed data, so no replacement of the metric terms or hidden normalization is introduced. The quadratic-log and 49/8 scalar conclusions preserve their index/level, finite-intersection, model and Arakelov inputs.

The global compact curve, actual differential-energy measures, their global (i/2) normalization, exact chart density identities, actual G identification, and finite/Arakelov geometry remain explicit producers. This constructor does not claim to construct those objects or prove the full FiveContact49Height statement. No mismatch or overstated theorem scope was found. No source or repository files were edited.
