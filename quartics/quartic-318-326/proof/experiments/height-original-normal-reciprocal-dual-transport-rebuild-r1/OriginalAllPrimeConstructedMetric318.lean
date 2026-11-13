module
public import OriginalConstructedExcludedGenerators318
public import OriginalConstructedMetricSections318
public section
noncomputable section
namespace OriginalAllPrimeConstructedMetric318
open NumberField SectionHeight318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
abbrev K := ContactOriginalMetricConsumer318.PointField c u v
abbrev t := ContactOriginalMetricConsumer318.coordinate u v
abbrev hn := ContactOriginalMetricConsumer318.avoidance c u v hf
variable (arch : InfinitePlace (K c u v) → ℝ) (harchPos : ∀ w,0<arch w)

/-- The good-place canonical lattice is retained. The finitely many
excluded-place lattices now come from actual integral zoom fibers. This
assembled frame is not yet identified with global arithmetic duality. -/
@[expose] def canonical : FrameNorms (K c u v) :=
  OriginalConstructedMetricSections318.canonical c u v hf i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) arch harchPos

theorem finite_integral (w : FinitePlace (K c u v)) (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
      ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*
        (canonical c u v hf i arch harchPos).finiteNorm w≤1 :=
  OriginalFiniteNormAssembly318.original_bound c (t u v) (hn c u v hf) i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) w n

theorem canonical_good (w : FinitePlace (K c u v))
    (hw : w (ContactArithmeticDenominator318.denominator c : K c u v)=1) :
    (canonical c u v hf i arch harchPos).finiteNorm w=
      OriginalGoodPlaceCotangentNorms318.finiteNorm c (t u v) (hn c u v hf) w hw i :=
  OriginalConstructedMetricSections318.canonical_good c u v hf i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) arch harchPos w hw

/-- No excluded-place generator or finite-integrality premise remains.
The remaining displayed assumptions are the genuine GLOBAL Hodge degree,
KS identification for this very assembled frame, and archimedean bound. -/
@[expose] def metricSections (hodge : FrameNorms (K c u v)) (hYuan : ℝ)
    (hdegree : hodge.normalizedDegree=hYuan)
    (hks : InducedLattice318.induced (canonical c u v hf i arch harchPos)
      (210 : K c u v) (by norm_num)=InducedLattice318.square hodge)
    (harch : ∀ (w : InfinitePlace (K c u v)) (n : Fin 2),
      w (![ContactBicanonicalPointHeight318.a0 c (t u v) (hn c u v hf) i,
        ContactBicanonicalPointHeight318.a1 c (t u v) (hn c u v hf) i] n)*arch w≤
          ContactMetricSections318.sectionBound) :
    RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  OriginalConstructedMetricSections318.metricSections c u v hf i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i)
    arch harchPos hodge hYuan hdegree hks harch
end OriginalAllPrimeConstructedMetric318
