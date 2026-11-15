module
public import OriginalArchimedeanBranchDerivative318
public import PELOriginalLiteralSectionBounds318
public import ContactMetricSections318
public section
noncomputable section
namespace OriginalArchimedeanFrameNorm318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanMarkedPoint318
open OriginalArchimedeanSectionCoefficient318 FourRootNormalizedPointCharts318
open LiteralMetricExtension318 PELOriginalManuscriptNormalization318 PeterssonSectionNorm318
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t))

@[expose] def density : ℝ := HolomorphicPoincare318.coefficient
  ((PELOriginalLiteralSectionBounds318.metricData hλ hμ).uniformizer (completedPoint c t w)) (0,0)
lemma density_pos : 0<density hλ hμ c t w :=
  HolomorphicPoincare318.coefficient_positive _
    ((PELOriginalLiteralSectionBounds318.metricData hλ hμ).upper _)
    ((PELOriginalLiteralSectionBounds318.metricData hλ hμ).noncritical _)

/-- Norm of the square of the ORIGINAL marked branch-coordinate
cotangent frame. Its multiplier is proved to be the actual marked-root
derivative in exists_chart, and its metric is the original uniformizer. -/
@[expose] def frameNorm (i : Fin 4) : ℝ :=
  quadraticNorm (density hλ hμ c t w) (branchDerivative c t w i^2)
include hn in
lemma frameNorm_pos (i : Fin 4) : 0<frameNorm hλ hμ c t w i := by
  unfold frameNorm quadraticNorm
  have hd := density_pos hλ hμ c t w
  have hs : 0<Real.sqrt (density hλ hμ c t w) := Real.sqrt_pos.2 hd
  exact mul_pos (norm_pos_iff.mpr (pow_ne_zero _ (branchDerivative_ne c t hn w i)))
    (sq_pos_of_pos (div_pos (by norm_num) hs))

lemma scalar_norm (i : Fin 4) (a : K c t) :
    w a*frameNorm hλ hμ c t w i=
      quadraticNorm (density hλ hμ c t w) (w.embedding a*branchDerivative c t w i^2) := by
  rw [quadraticNorm_mul,InfinitePlace.norm_embedding_eq]
  rfl

/-- The quantitative analytic theorem is now specialized to the SAME
actual number-field point and the SAME two original global section
values in their original branch frame, at every infinite place. -/
theorem section_bounds (i : Fin 4) :
    w (ContactBicanonicalPointHeight318.a0 c t hn i)*frameNorm hλ hμ c t w i≤
      ContactMetricSections318.sectionBound ∧
    w (ContactBicanonicalPointHeight318.a1 c t hn i)*frameNorm hλ hμ c t w i≤
      ContactMetricSections318.sectionBound := by
  let p := completedPoint c t w
  obtain ⟨h,hk⟩ := (LiteralContactMetricCharts318.data p).regular_kind (regular c t hn w)
  have hk' : (PELOriginalLiteralSectionBounds318.metricData hλ hμ).kind p=
      SourceMetricCharts318.Chart.regular (t:ℂ) (coordinate_ne c t hn) := by
    exact hk
  have hb := PELOriginalLiteralSectionBounds318.integral_section_norms hλ hμ p
  rw [hk'] at hb
  change quadraticNorm (density hλ hμ c t w)
      ((2765952000:ℂ)^2*BicanonicalCharts318.q0 contacts (t:ℂ))≤_ ∧
    quadraticNorm (density hλ hμ c t w)
      ((2765952000:ℂ)^2*BicanonicalCharts318.q1 contacts (t:ℂ))≤_ at hb
  rw [scalar_norm,scalar_norm,(scaled_coordinates c t hn w i).1,(scaled_coordinates c t hn w i).2]
  exact hb

theorem all_sections (i : Fin 4) (n : Fin 2) :
    w (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*frameNorm hλ hμ c t w i≤
      ContactMetricSections318.sectionBound := by
  fin_cases n
  · exact (section_bounds hλ hμ c t hn w i).1
  · exact (section_bounds hλ hμ c t hn w i).2
end OriginalArchimedeanFrameNorm318
