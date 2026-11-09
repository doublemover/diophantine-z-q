# Independent source-curve audit

Snapshot: branch commit590a7679f39286fdf1bfbbd3f5a0ab765a2bb277. This is a bounded source/dependency audit, not a new Lean validation. No historical source modified.

## Finding
No j-map source frame or elliptic open-j Hodge frame is consumed by the inspected original contact metric chain. The missing contact complex atlas, archimedean comparison, and quaternionic/PEL Hodge/KS identification remain explicit unconstructed interfaces. This does not establish those remaining inputs.

## Exact source evidence
- progress/SourceMetricCharts318.lean:12–23 defines formal regular/finite-branch/infinity coefficient kinds and explicitly disclaims geometric realization. Lines49–57 require actual compact charts, a global ratio, its local identity, and hyperbolic metric data. These are not supplied by a ThreeJ chart.
- progress/GlobalSectionNorm318.lean:12–25 and UniformizingSectionBounds318.lean:13–27 retain the geometric chart/ratio interface. The latter adds actual analytic upper-half-plane uniformizers/noncriticality as INPUTS. The scalar curvature/section estimates do not construct an atlas.
- experiments/forward-three-j-reciprocal-kernel-r9/ThreeJManifoldHolomorphy318.lean:9–20 explicitly uses ProjectiveLine/ActualThree ComplexPoints, its original two charts, and the genus-zero j-map. It does not assert contact-curve charts. No ThreeJ module occurs in the inspected metric import closure.
- progress/ContactDifferentialFrames318.lean:31–46 uses actual ramified root coordinate and SourceOrder principal localization;55–62 uses the actual attached infinity order. Neither is a j-map cotangent frame.
- progress/ContactProjectiveLinePullback318.lean:14–37 explicitly pulls separately constructed target O(1) along the original contact bicanonical projective map, with branch/infinity squares. JLineAtlas here is the generic P1 TARGET atlas, not a replacement source atlas.
- progress/IntrinsicHodgeComparison318.lean:90–111 defines pushforward of genuine Weierstrass relative differentials and its identity evaluation, then specializes to OpenJAffineScheme A/B. progress/LiteralIntrinsicHodge318.lean:20–40 is explicitly that elliptic open-j family. It proves neither the contact curve Hodge frame nor the quaternionic surface Hodge/KS identity. Searches of accepted top-level sources find no use of LiteralIntrinsicHodge318 outside its definition; IntrinsicHodgeIsomorphism318 is only instantiated there. No such module occurs in the original metric closure.
- experiments/height-original-metric-assembly-r2/ContactOriginalMetricConsumer318.lean:48–62 expressly does not identify a PEL field or assert metric inputs exist. Hodge FrameNorms, degree, exact210 KS equality and arch estimates are explicit inputs.
- same packet/OriginalConstructedMetricSections318.lean:24–45 constructs the good finite-place part but still requires excluded-place generators/membership, arch bound, Hodge degree and exact KS equality. No elliptic Hodge frame is assigned there.
- progress/RefinedContactRealization318.lean:14–26 makes those geometric metric data explicit fields. InducedLattice318.lean:79–88 derives the degree formula CONDITIONALLY from actual all-place norm equality; it does not construct a Kodaira–Spencer map.

## Impact and remaining work
No checked theorem needs withdrawal or source repair from this audit. Earlier claims of a completed contact analytic atlas, full archimedean height realization, or PEL Hodge/KS identification would exceed the actual statements. The next actual contact-curve complex-chart work fills an existing explicit gap; the checked code does not show a prior contact atlas silently replaced by the j-map atlas. Existing local coefficient/curvature lemmas and elliptic open-j Hodge lemmas retain their stated scopes. Continue actual contact atlas and original metric attachment; separately construct the required quaternionic/PEL Hodge/KS comparison.
