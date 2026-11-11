module
public import PELOriginalCandidateNormalizationLocalInjection318
public import WholeRootOpenSectionSimple318
public section
noncomputable section
namespace PELOriginalNormalizationRootSection318
open Set Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalFiniteUnramifiedProjection318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The inverse of the SAME actual normalization produces a continuous
root section on an honest open base neighborhood. The full chart-ring
element t is evaluated on actual original points throughout. -/
theorem exists_root_section
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (e : OpenPartialHomeomorph ComplexVectors ComplexVectors)
    (he : ∀ y, e y = evaluationVector τ hτ j g y) (hxe : x ∈ e.source)
    (t : CoordinateChart τ hτ j) (Q : Polynomial (MvPolynomial (Fin 2) ℂ))
    (hQ : ∀ z : ComplexVectors, value τ hτ 3 j z ≠ 0 →
      (Q.map (MvPolynomial.eval (evaluationVector τ hτ j g z))).IsRoot
        (evaluate τ hτ j t z)) :
    ∃ W : Set ComplexVectors, ∃ hW : IsOpen W,
      ∃ hxW : evaluationVector τ hτ j g x ∈ W,
      ∃ b : W → ℂ, Continuous b ∧
        b ⟨evaluationVector τ hτ j g x,hxW⟩ = evaluate τ hτ j t x ∧
        ∀ y : W, (Q.map (MvPolynomial.eval y.val)).IsRoot (b y) := by
  let D : Set ComplexVectors := e.source ∩ {z | value τ hτ 3 j z ≠ 0}
  have hD : IsOpen D := e.open_source.inter
    (isOpen_ne (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous continuous_const)
  let W : Set ComplexVectors := e '' D
  have hW : IsOpen W := e.isOpen_image_of_subset_source hD inter_subset_left
  have hxW : evaluationVector τ hτ j g x ∈ W := ⟨x,⟨hxe,hx⟩,he x⟩
  have hWt : W ⊆ e.target := by
    rintro y ⟨z,hz,rfl⟩
    exact e.map_source hz.1
  have inverse_mem (y : W) : e.symm y.val ∈ D := by
    obtain ⟨z,hz,hzy⟩ := y.property
    rw [←hzy,e.left_inv hz.1]
    exact hz
  have hi : Continuous (fun y : W => e.symm y.val) :=
    (e.symm.continuousOn.mono hWt).continuous_restrict
  let b : W → ℂ := fun y => evaluate τ hτ j t (e.symm y.val)
  have hb : Continuous b := continuous_iff_continuousAt.mpr (fun y =>
    ContinuousAt.comp (f := fun q : W => e.symm q.val)
      (g := evaluate τ hτ j t) (x := y)
      (contDiffAt_evaluate τ hτ j t (e.symm y.val) (inverse_mem y).2).continuousAt
      hi.continuousAt)
  refine ⟨W,hW,hxW,b,hb,?_,?_⟩
  · change evaluate τ hτ j t (e.symm (evaluationVector τ hτ j g x)) = _
    rw [←he x,e.left_inv hxe]
  · intro y
    have hbase : evaluationVector τ hτ j g (e.symm y.val) = y.val := by
      rw [←he,e.right_inv (hWt y.property)]
    simpa only [hbase,b] using hQ (e.symm y.val) (inverse_mem y).2
end PELOriginalNormalizationRootSection318
