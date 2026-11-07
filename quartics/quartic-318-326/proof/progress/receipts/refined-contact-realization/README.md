# Refined actual five-contact realization

Strict-kernel PASS: two modules, nine public theorems and 127 exhaustively audited declarations. Most declarations in the second module are generated record projections, not additional geometric results. Only propext, Classical.choice and Quot.sound occur.

## Actual degree arithmetic

`InducedLattice318.induced F c hc` retains the infinite frame norms and divides the finite frame norm by the actual finite absolute value of c. It represents the induced metric on the lattice cM using the same generic frame. It is not the earlier frame-rescaling operation, which preserves degree.

The product formula proves the exact degree correction. For a positive integer n,

    degree(nM with induced metric) = degree(M) - log n.

The tensor-square frame has degree twice the original degree. Equality of the actual induced210 frame norms with the squared Hodge frame norms then gives

    degree(omega_max^2) = 2 degree(lambda_A) + log210.

Thus the sign and factor are derived from actual NumberField places rather than retained as a supplied scalar degree identity.

## Refined producer contract

`MetricSections K u v hYuan` contains actual two section coordinates in K, their rational ratio 32u/v, a nonzero first coordinate, actual canonical and Hodge frame norms, Hodge height identification, KS image-lattice equality, finite integrality and the exact archimedean section bound. It has no contact-height inequality or scalar KS degree identity field.

`MetricSections.original_bound` and `.shifted_bound` derive the contact comparisons through the already checked section-to-height theorem. The CM input record uses original L2 surface height, so its section data have hYuan=hOriginal+log(pi). The non-CM record uses the shifted surface height directly. The two input records omit the old contact_metric field; their `.toLegacy` constructors populate it only after proving it from these actual data.

`five_contact_of_refined_realization` proves the exact ContactHeight318.FiveContact49Height predicate from `RefinedGeometricRealization`. The auxiliary section field is quantified independently from the non-CM model/averaging field K, CM averaging degree and both controlled isogeny field degrees.

## Formal boundary

`RefinedGeometricRealization` is **not proved or axiomatized**. An actual geometric construction must still instantiate the records, including the genuine arithmetic models, frame norms and their Hodge/KS interpretation, periods, Arakelov identities and isogeny applications. The new result replaces an intermediate scalar contact inequality and a scalar KS degree formula with more concrete actual local norm data, and proves the remaining degree/height arithmetic. It is not an unconditional Lean proof of the global geometric theorem.

For the classical interpretation of the KS norm equality, choose a nonzero rational Hodge frame eta and use psi3(eta^2) as the generic canonical-line frame. The isometry onto210*omega_max^2 identifies its induced image-lattice norms with the squared Hodge norms at every place. This is an application of the actual map, not a choice of a level-three dualizing line or an assumption about a cover degree. `maximal-ks-producer/MAXIMAL-KS-PRODUCER.md` supplies the actual model/application ledger.

Run `bash build.sh` to rebuild both modules and perform the exhaustive audit. Imported dependencies use the recorded shared cache; this is not a fresh full dependency-closure replay. No repository or Git changes were made.
