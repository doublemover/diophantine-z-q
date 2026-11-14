module
public import PELOriginalFiniteFirstJetNormalization318
public import OpenComplexPolynomialIndependence318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public section
noncomputable section
namespace PELOriginalFiniteUnramifiedProjection318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalChartTangentDerivation318
open Filter Topology Set
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

@[expose] def evaluationVector
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j) :
    ComplexVectors → ComplexVectors := fun y k => evaluate τ hτ j (g (MvPolynomial.X k)) y

lemma evaluation_contDiffAt
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    ContDiffAt ℂ 1 (evaluationVector τ hτ j g) x :=
  contDiffAt_pi.mpr fun k => contDiffAt_evaluate τ hτ j (g (MvPolynomial.X k)) x hx

lemma evaluation_derivative
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (hjet : ∀ v : ComplexVectors, ∀ k : Fin 2,
      tangentDerivation τ hτ x j hx v (g (MvPolynomial.X k)) = v k) :
    HasFDerivAt (evaluationVector τ hτ j g) (ContinuousLinearMap.id ℂ ComplexVectors) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  have he : fderiv ℂ (evaluate τ hτ j (g (MvPolynomial.X k))) x =
      (ContinuousLinearMap.proj k : ComplexVectors →L[ℂ] ℂ) := by
    ext v
    exact (tangentDerivation_apply τ hτ x j hx v _).symm.trans (hjet v k)
  have hd := ((contDiffAt_evaluate τ hτ j (g (MvPolynomial.X k)) x hx).differentiableAt
    (by norm_num)).hasFDerivAt
  simpa only [he] using hd

/-- An actual analytic inverse neighborhood makes the SAME whole
normalization algebra map faithful. No generic dimension shortcut is
used to infer injectivity after changing normalization coordinates. -/
lemma injective_of_identity_jet
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (hjet : ∀ v : ComplexVectors, ∀ k : Fin 2,
      tangentDerivation τ hτ x j hx v (g (MvPolynomial.X k)) = v k) :
    Function.Injective g := by
  let F := evaluationVector τ hτ j g
  have hF := evaluation_contDiffAt τ hτ j g x hx
  have hd := evaluation_derivative τ hτ j g x hx hjet
  let e := hF.toOpenPartialHomeomorph F hd (by norm_num)
  have hxe : x ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  let U := e.source ∩ {y : ComplexVectors | value τ hτ 3 j y ≠ 0}
  have hU : IsOpen U := e.open_source.inter
    (isOpen_ne (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous continuous_const)
  have hW : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU inter_subset_left
  have hind : AlgebraicIndependent ℂ (fun k : Fin 2 => g (MvPolynomial.X k)) := by
    apply OpenComplexPolynomialIndependence318.independent_of_open_evaluations
      _ (e '' U) hW ⟨e x,⟨x,⟨hxe,hx⟩,rfl⟩⟩
    rintro w ⟨y,hy,rfl⟩
    refine ⟨algebraEvaluation τ hτ y j hy.2,?_⟩
    intro k
    change algebraEvaluation τ hτ y j hy.2 (g (MvPolynomial.X k)) =
      evaluate τ hτ j (g (MvPolynomial.X k)) y
    exact (evaluate_on_chart τ hτ j _ y hy.2).symm
  have hg : MvPolynomial.aeval (fun k : Fin 2 => g (MvPolynomial.X k)) = g := by
    ext k
    simp only [MvPolynomial.aeval_X]
  rw [algebraicIndependent_iff_injective_aeval,hg] at hind
  exact hind

/-- At EVERY actual original point in EVERY nonzero theta chart there
is a WHOLE finite faithful polynomial normalization, an actual identity
derivative on the original analytic tangent, and a genuine local inverse
chart centered at that same point. This does not yet claim that the
candidate scheme itself is etale or smooth at the point. -/
theorem exists_finite_faithful_identity_chart
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0) :
    ∃ g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      g.Finite ∧ Function.Injective g ∧
      HasFDerivAt (evaluationVector τ hτ j g) (ContinuousLinearMap.id ℂ ComplexVectors) x ∧
      ∃ e : OpenPartialHomeomorph ComplexVectors ComplexVectors,
        (∀ y, e y = evaluationVector τ hτ j g y) ∧ x ∈ e.source ∧
        ContDiffAt ℂ 1 e.symm (evaluationVector τ hτ j g x) := by
  obtain ⟨g,hfinite,hjet,hcenter⟩ :=
    PELOriginalFiniteFirstJetNormalization318.exists_finite_identity_jet τ hτ x j hx
  have hd := evaluation_derivative τ hτ j g x hx hjet
  have hF := evaluation_contDiffAt τ hτ j g x hx
  let e := hF.toOpenPartialHomeomorph (evaluationVector τ hτ j g) hd (by norm_num)
  refine ⟨g,hfinite,injective_of_identity_jet τ hτ j g x hx hjet,hd,e,
    fun y => rfl,?_,?_⟩
  · exact hF.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  · exact hF.to_localInverse hd (by norm_num)
end PELOriginalFiniteUnramifiedProjection318
