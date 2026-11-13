module
public import OriginalArchimedeanFrameNorm318
public import OriginalConstructedMetricSections318
public section
noncomputable section
namespace OriginalConstructedArchimedeanSections318
open NumberField SectionHeight318 OriginalExcludedPlaceData318 PELOriginalManuscriptNormalization318
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
abbrev t := ContactOriginalMetricConsumer318.coordinate u v
abbrev hn := ContactOriginalMetricConsumer318.avoidance c u v hf
abbrev K := ContactOriginalMetricConsumer318.PointField c u v
@[expose] def arch (w : InfinitePlace (K c u v)) : ℝ :=
  OriginalArchimedeanFrameNorm318.frameNorm hλ hμ c (t u v) w i
include hf in
lemma arch_pos (w : InfinitePlace (K c u v)) : 0<arch hλ hμ c u v i w :=
  OriginalArchimedeanFrameNorm318.frameNorm_pos hλ hμ c (t u v) (hn c u v hf) w i

/-- The previous final interface's entire archimedean input is produced
from actual original signed points, their genuine branch-coordinate
derivatives and the original uniformizing metric. Excluded finite-place
generators and the actual global Hodge/KS comparison remain explicit. -/
@[expose] def metricSections
    (B : ExcludedGenerators c (t u v) (hn c u v hf) i)
    (hodge : FrameNorms (K c u v)) (hYuan : ℝ)
    (hdegree : hodge.normalizedDegree=hYuan)
    (hks : InducedLattice318.induced
      (OriginalConstructedMetricSections318.canonical c u v hf i B
        (arch hλ hμ c u v i) (arch_pos hλ hμ c u v hf i))
      (210:K c u v) (by norm_num)=InducedLattice318.square hodge) :
    RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  OriginalConstructedMetricSections318.metricSections c u v hf i B
    (arch hλ hμ c u v i) (arch_pos hλ hμ c u v hf i) hodge hYuan hdegree hks
    (fun w n => OriginalArchimedeanFrameNorm318.all_sections hλ hμ c (t u v)
      (hn c u v hf) w i n)
end OriginalConstructedArchimedeanSections318
