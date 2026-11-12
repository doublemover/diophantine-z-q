module
public import PELOriginalDegreeOneRatioTopology318
public section
noncomputable section
namespace PELOriginalDegreeOneRatioHolomorphy318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalDegreeOneRatioBundle318 PELOriginalDegreeOneRatioTopology318
variable (τ : ℂ) (hτ : 0<τ.im)

@[expose] def originalCoordinates (b : ComplexVectors)
    (p : PELOriginalPolarizationLineBundle318.Total τ hτ) : ComplexVectors × ℂ :=
  (chart τ hτ b p.1,((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv b p).2)
@[expose] def mixedCoordinates (b : ComplexVectors) (a : Index)
    (p : MixedTotal τ hτ) : ComplexVectors × ℂ :=
  (chart τ hτ b p.1,((mixedCore τ hτ).localTriv a p).2)
@[expose] def localRatio (a : Index) (z : ComplexVectors) : ℂ :=
  value τ hτ 3 a.1 z/value τ hτ 2 a.2 z
@[expose] def forwardLocal (a : Index) (p : ComplexVectors × ℂ) : ComplexVectors × ℂ :=
  (p.1,p.2/localRatio τ hτ a p.1)
@[expose] def inverseLocal (a : Index) (p : ComplexVectors × ℂ) : ComplexVectors × ℂ :=
  (p.1,localRatio τ hτ a p.1*p.2)

lemma coefficient_original (b : ComplexVectors) (a : Index) (q : Base τ)
    (hb : q∈baseSet τ hτ b) :
    sectionCoefficient τ hτ b a q=localRatio τ hτ a (chart τ hτ b q) := by
  rw [sectionCoefficient,localRatio,
    PELOriginalHyperplanePullbackHolomorphy318.coefficient_original τ hτ 1 b a.1 q hb,
    PELOriginalHyperplanePullbackHolomorphy318.coefficient_original τ hτ 0 b a.2 q hb]

/-- Exact degree-one forward formula in genuine original covering
coordinates and the independent mixed hyperplane atlas. -/
theorem forward_coordinate_identity (b : ComplexVectors) (a : Index)
    (p : PELOriginalPolarizationLineBundle318.Total τ hτ)
    (hb : p.1∈baseSet τ hτ b) (ha : p.1∈domain τ hτ a) :
    mixedCoordinates τ hτ b a (homeomorph τ hτ p) =
      forwardLocal τ hτ a (originalCoordinates τ hτ b p) := by
  apply Prod.ext
  · rfl
  · change _=_/localRatio τ hτ a (chart τ hτ b p.1)
    rw [original_chart_ratio τ hτ b p.1 hb a ha p.2,
      ←coefficient_original τ hτ b a p.1 hb]
    rfl

theorem inverse_coordinate_identity (b : ComplexVectors) (a : Index) (p : MixedTotal τ hτ)
    (hb : p.1∈baseSet τ hτ b) (ha : p.1∈domain τ hτ a) :
    originalCoordinates τ hτ b ((homeomorph τ hτ).symm p) =
      inverseLocal τ hτ a (mixedCoordinates τ hτ b a p) := by
  apply Prod.ext
  · rfl
  · exact (inverse_coordinate τ hτ b a p hb ha).trans
      (congrArg (fun c : ℂ => c*((mixedCore τ hτ).localTriv a p).2)
        (coefficient_original τ hτ b a p.1 hb))

lemma localRatio_holomorphic (a : Index) (z : ComplexVectors)
    (h2 : value τ hτ 2 a.2 z≠0) : DifferentiableAt ℂ (localRatio τ hτ a) z :=
  (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 a.1 z).div
    (PELOriginalLevelPowerSections318.holomorphic τ hτ 2 a.2 z) h2

lemma forward_holomorphic (a : Index) (p : ComplexVectors × ℂ)
    (h3 : value τ hτ 3 a.1 p.1≠0) (h2 : value τ hτ 2 a.2 p.1≠0) :
    DifferentiableAt ℂ (forwardLocal τ hτ a) p :=
  differentiableAt_fst.prodMk (differentiableAt_snd.div
    ((localRatio_holomorphic τ hτ a p.1 h2).comp p differentiableAt_fst) (div_ne_zero h3 h2))

lemma inverse_holomorphic (a : Index) (p : ComplexVectors × ℂ)
    (h2 : value τ hτ 2 a.2 p.1≠0) : DifferentiableAt ℂ (inverseLocal τ hτ a) p :=
  differentiableAt_fst.prodMk
    (((localRatio_holomorphic τ hτ a p.1 h2).comp p differentiableAt_fst).mul differentiableAt_snd)

/-- Both local maps of the SAME actual total-space homeomorphism are
holomorphic, with the literal original theta3/theta2 quotient. This
identifies the independent 3−2 bundle with the ORIGINAL polarization
line, not merely a line of equal rank or the same cube. -/
theorem actual_local_biholomorphy (b : ComplexVectors) (a : Index)
    (p : PELOriginalPolarizationLineBundle318.Total τ hτ)
    (hb : p.1∈baseSet τ hτ b) (ha : p.1∈domain τ hτ a) :
    DifferentiableAt ℂ (forwardLocal τ hτ a) (originalCoordinates τ hτ b p) ∧
    DifferentiableAt ℂ (inverseLocal τ hτ a) (mixedCoordinates τ hτ b a (homeomorph τ hτ p)) := by
  have h3 : value τ hτ 3 a.1 (chart τ hτ b p.1)≠0 := by
    rw [←PELOriginalHyperplanePullbackHolomorphy318.coefficient_original τ hτ 1 b a.1 p.1 hb]
    exact PELOriginalHyperplanePullbackTopology318.coefficient_ne τ hτ 1 b a.1 p.1 ha.1
  have h2 : value τ hτ 2 a.2 (chart τ hτ b p.1)≠0 := by
    rw [←PELOriginalHyperplanePullbackHolomorphy318.coefficient_original τ hτ 0 b a.2 p.1 hb]
    exact PELOriginalHyperplanePullbackTopology318.coefficient_ne τ hτ 0 b a.2 p.1 ha.2
  exact ⟨forward_holomorphic τ hτ a _ h3 h2,inverse_holomorphic τ hτ a _ h2⟩
end PELOriginalDegreeOneRatioHolomorphy318
