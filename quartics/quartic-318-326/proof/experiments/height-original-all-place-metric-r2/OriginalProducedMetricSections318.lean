module
public import OriginalAllPlaceProducedNorms318
public section
noncomputable section
namespace OriginalProducedMetricSections318
open NumberField SectionHeight318 PELOriginalManuscriptNormalization318
open OriginalAllPlaceProducedNorms318
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
variable (hodge : FrameNorms (K c u v)) (hYuan : ℝ)
  (hdegree : hodge.normalizedDegree=hYuan)
  (hks : InducedLattice318.induced (norms hλ hμ c u v hf i)
    (210:K c u v) (by norm_num)=InducedLattice318.square hodge)

/-- The final original metric record with NO supplied arch estimate,
finite bound or excluded lattice generator. Only the genuine Hodge
degree and KS identification with this EXACT produced family remain,
in addition to explicit original numerical character identification. -/
@[expose] def sections : RefinedContactRealization318.MetricSections (K c u v) u v hYuan :=
  OriginalAllPrimeConstructedMetric318.metricSections c u v hf i
    (OriginalConstructedArchimedeanSections318.arch hλ hμ c u v i)
    (OriginalConstructedArchimedeanSections318.arch_pos hλ hμ c u v hf i)
    hodge hYuan hdegree hks (arch_bound hλ hμ c u v hf i)

include hdegree hks in
/-- Contact metric is a CONCLUSION, never a premise. The remaining
hypothesis is equality of all actual local norms in the KS image. -/
theorem original_bound : ContactHeight318.pointHeight u v<
    2*(hYuan-Real.log Real.pi)+120 :=
  (sections hλ hμ c u v hf i hodge hYuan hdegree hks).original_bound

include hdegree hks in
theorem shifted_bound : ContactHeight318.pointHeight u v≤2*hYuan+120 :=
  (sections hλ hμ c u v hf i hodge hYuan hdegree hks).shifted_bound
end OriginalProducedMetricSections318
