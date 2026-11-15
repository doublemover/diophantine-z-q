# Producer audit at published 2b151fc6

## Exact formal consumer

`FiveContactProducer318.GeometricRealization` quantifies every coprime integer pair with all five homogeneous forms nonzero. It requires CM producer data or a number field with NonCM producer data. `RefinedContactRealization318.RefinedGeometricRealization` replaces the scalar contact bound by actual `MetricSections`, but still requires these data for each point; `refined_implies_legacy` is conditional.

`MetricSections` contains actual section values, ratio/nonvanishing, canonical and Hodge norms, Hodge degree, exact all-local-norm KS identity, all infinite-place bounds and all finite-place integrality. A scalar degree equality alone does not suffice.

## Constructed formal chain, not proof-status claim

The published lattice packet's source constructs the original point and section values, good-place cotangent normalizers/lattices, and finite support. `OriginalSectionLatticeGeneration318.original_pair_span` identifies the full original pair's span with the same good-place cotangent lattice, not just an abstract line. `OriginalCanonicalFiniteLattices318` assembles exact embedded lattices from those good generators and a residual bad-place record. `KSImageFrameNorms318` derives norm equality and the +log210 degree from all-place image equality. `OriginalKSLatticeMetricSections318.metricSections` routes these exact data to the original metric-section consumer.

This describes source dependencies, not current kernel acceptance of the entire chain: hosted execution still stops at CommonRestriction earlier in the r16 dependency order.

## Residual formal assumptions

`OriginalExcludedPlaceData318.ExcludedGenerators` still supplies all bad generators, nonvanishing and original membership. Its own documentation denies bad-model or Hodge/KS provenance. `OriginalConstructedMetricSections318` supplies Hodge norms, degree, KS identity and archimedean bound. `OriginalKSLatticeMetricSections318` removes the norm-equality premise only by replacing it with **all-place embedded KS-image equalities**, plus specified Hodge generators/metrics, Hodge degree and all archimedean inputs. No global Hodge or bad-model existence follows from these interfaces.

## Actual Hodge construction found, but on a different object

`IntrinsicHodgeComparison318.hodge` is the pushforward of genuine relative differentials on the completed Weierstrass family; its canonical evaluation at the identity is explicitly built from the pullback/pushforward adjunction. `IntrinsicHodgeIsomorphism318` proves invertibility for a smooth domain-base completed Weierstrass family using proved global frames and structure-function descent. `LiteralIntrinsicHodge318` specializes this to the literal open-j family. These are genuine constructions, but they are elliptic-family Hodge lines over a localized base, not the actual quaternionic surface determinant on the maximal integral stack, nor its all-place metrized evaluation at this original point. Substituting the former for the latter would change the object.

## Historical application found; formal bridge remains pending

Read the actual `receipts/maximal-ks-producer/MAXIMAL-KS-PRODUCER.md`, not just its receipt status. It describes the classical Yuan application on the maximal stack over Z: the actual surface after forgetting level, determinant line, integral image 210 times the canonical square, induced metric, normalized degree sign and absence of a level or ramification correction. It explicitly disclaims a Lean stack/Arakelov construction. It retains actual fiber/moduli construction, integral extension, original global sections and archimedean estimates as prior inputs.

Historical classification for this audit: **prior classical connecting argument found**, with the note's retained inputs not independently re-proved here. Formal manuscript/code classification: **partly incorporated; actual per-point global producers and their formal comparison remain pending**. No assertion is made that this is a newly discovered mathematical gap or that the classical argument is invalid. The primary Yuan PDF and the separate retained fiber/metric packets have not been freshly re-audited in this slice, so this audit does not independently reaccept the global classical theorem application.

## New slice and remaining boundary

The new slice derives scalar generators from independently supplied actual embedded model frames, and derives image equality from independently supplied normalized linear comparison maps. It proves those outputs reach the existing exact original-section consumer. It does not construct the input embedded model lattices, frames, KS comparisons, surface Hodge determinant/metric, degree identity, archimedean data or CM/non-CM records. No target-derived Hodge metric, arbitrary auxiliary lattice substitution, smaller set of places or covert per-point existence choice is used.

The normalized local comparison direction is canonical lattice to Hodge-product lattice with coefficient 210. Relating this normalized local inverse/image identification to Yuan's native Hodge-square-to-canonical-square injection is an explicit remaining global comparison obligation, not an automatic naming convention.
