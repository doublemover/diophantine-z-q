module
public import OriginalModelFrameNorms318
public import ContactOriginalMetricConsumer318
public section
noncomputable section
namespace OriginalConstructedMetricSections318
open NumberField SectionHeight318 OriginalExcludedPlaceData318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5, ContactRadical318.forms u v j≠0) (i : Fin 4)
abbrev t := ContactOriginalMetricConsumer318.coordinate u v
abbrev hn := ContactOriginalMetricConsumer318.avoidance c u v hf
abbrev K := ContactOriginalMetricConsumer318.PointField c u v
variable (B : ExcludedGenerators c (t u v) (hn c u v hf) i)
  (arch : InfinitePlace (K c u v) → ℝ) (harchPos : ∀ w, 0<arch w)
@[expose] def canonical : FrameNorms (K c u v) :=
  OriginalModelFrameNorms318.frame c (t u v) (hn c u v hf) i B arch harchPos

/-- The ORIGINAL final metric-section interface now receives a constructed
good-place lattice family and a derived global finite-support proof.
Only the displayed excluded-place generators, archimedean estimate, and
actual Hodge/KS identification remain inputs. In particular this is not an
assertion that those remaining geometric inputs have been realized. -/
@[expose] def metricSections
    (hodge : FrameNorms (K c u v)) (hYuan : ℝ)
    (hdegree : hodge.normalizedDegree=hYuan)
    (hks : InducedLattice318.induced (canonical c u v hf i B arch harchPos)
      (210:K c u v) (by norm_num)=InducedLattice318.square hodge)
    (harch : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  ContactOriginalMetricConsumer318.metricSections c u v hf i
    (canonical c u v hf i B arch harchPos) hodge hYuan hdegree hks harch
    (OriginalFiniteNormAssembly318.original_bound c (t u v) (hn c u v hf) i B)

/-- The retained canonical metric is exactly the assembled one, including
the proved original good-place cotangent lattices. -/
theorem canonical_good (w : FinitePlace (K c u v))
    (hw : w (ContactArithmeticDenominator318.denominator c:K c u v)=1) :
    (canonical c u v hf i B arch harchPos).finiteNorm w=
      OriginalGoodPlaceCotangentNorms318.finiteNorm c (t u v) (hn c u v hf) w hw i :=
  OriginalFiniteNormAssembly318.finiteNorm_good c (t u v) (hn c u v hf) i B w hw
end OriginalConstructedMetricSections318
