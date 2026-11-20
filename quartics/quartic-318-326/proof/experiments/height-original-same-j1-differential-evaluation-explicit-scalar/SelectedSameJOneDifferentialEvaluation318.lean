module
public import SelectedLiteralJOneDJ318
public import SelectedPrimitiveCenteredGerm318
public import SelectedJointRationalCenter318
public import SelectedJOneKaehlerEvaluation318
public section
noncomputable section
open Polynomial KaehlerDifferential Filter
open scoped TensorProduct Topology
open SelectedLiteralJOneDJ318 SelectedPrimitiveCenteredGerm318
open SelectedJointRationalCenter318 SelectedJOneKaehlerEvaluation318

namespace SelectedSameJOneDifferentialEvaluation318

variable (M : ℕ) (p : (R M)[X])

/-- The canonical rational-to-complex map of this exact root chart. -/
@[expose] def complexify : Rat M p →ₐ[ℚ] Cpx M p :=
  Algebra.TensorProduct.map (Algebra.ofId ℚ ℂ) (AlgHom.id ℤ (S M p))

theorem complexify_j : complexify M p (jRat M p) = jCpx M p := by
  simp only [complexify,jRat,jCpx,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]

/-- Actual functorial Kähler map along the scalar square Q→C. -/
@[expose] def pull (ω : KaehlerDifferential ℚ (Rat M p)) :
    KaehlerDifferential ℂ (Cpx M p) := by
  letI : Algebra (Rat M p) (Cpx M p) := (complexify M p).toRingHom.toAlgebra
  letI : IsScalarTower ℚ (Rat M p) (Cpx M p) := IsScalarTower.of_algHom (complexify M p)
  letI : SMulCommClass ℂ (Rat M p) (Cpx M p) := SMulCommClass.of_commMonoid ℂ (Rat M p) (Cpx M p)
  exact KaehlerDifferential.map ℚ ℂ (Rat M p) (Cpx M p) ω

theorem pull_dj (a : Rat M p) :
    pull M p (a • D ℚ (Rat M p) (jRat M p)) =
      complexify M p a • D ℂ (Cpx M p) (jCpx M p) := by
  letI : Algebra (Rat M p) (Cpx M p) := (complexify M p).toRingHom.toAlgebra
  letI : IsScalarTower ℚ (Rat M p) (Cpx M p) := IsScalarTower.of_algHom (complexify M p)
  letI : SMulCommClass ℂ (Rat M p) (Cpx M p) := SMulCommClass.of_commMonoid ℂ (Rat M p) (Cpx M p)
  change KaehlerDifferential.map ℚ ℂ (Rat M p) (Cpx M p)
    (a • D ℚ (Rat M p) (jRat M p)) = _
  rw [LinearMap.map_smul,IsScalarTower.algebraMap_smul,KaehlerDifferential.map_D]
  change complexify M p a • D ℂ (Cpx M p) (complexify M p (jRat M p)) = _
  rw [complexify_j]

/-- Complex evaluation of a rational regular representative is literal
extension of its same-root evaluation. -/
theorem same_eval_on_rational (b : S M p →+* ℂ) (a : Rat M p) :
    extendComplex b (complexify M p a) = rationalEval b a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r f =>
    simp only [complexify,Algebra.TensorProduct.map_tmul,Algebra.ofId_apply,
      AlgHom.id_apply,extendComplex_tmul,rationalEval_tmul]
  | add a b ha hb => simp only [map_add,ha,hb]

variable (b : ℂ → S M p →+* ℂ)

abbrev complexBranch (z : ℂ) : Cpx M p →ₐ[ℂ] ℂ :=
  extendComplex (b z)

theorem complexBranch_hol (hhol : ∀ f, AnalyticAt ℂ (fun z => b z f) 0) (a : Cpx M p) :
    DifferentiableAt ℂ (fun z => complexBranch M p b z a) 0 :=
  (extendComplex_analyticAt b 0 hhol a).differentiableAt

variable (hp : p.Monic) (hu : IsUnit (AdjoinRoot.mk p p.derivative))

/-- Across the actual centered j germ, the evaluated pullback of a rational
differential is evaluation of its same regular coefficient. No free
scalar, altered embedding, reselected minor or Hodge theorem enters. -/
theorem branch_evaluates_same_coefficient
    (hhol : ∀ f, AnalyticAt ℂ (fun z => b z f) 0)
    (hj : ∀ᶠ z in 𝓝 (0 : ℂ), b z (j M p) = 1+z)
    (ω : KaehlerDifferential ℚ (Rat M p)) :
    letI := pointAlgebra (complexBranch M p b)
    letI : IsScalarTower ℂ (Cpx M p) ℂ := IsScalarTower.of_algHom (complexBranch M p b 0)
    (branchDerivation (complexBranch M p b) (complexBranch_hol M p b hhol)).liftKaehlerDifferential
      (pull M p ω) = rationalEval (b 0) (rationalFrame M p hp hu ω) := by
  letI := pointAlgebra (complexBranch M p b)
  letI : IsScalarTower ℂ (Cpx M p) ℂ := IsScalarTower.of_algHom (complexBranch M p b 0)
  have hj' : ∀ᶠ z in 𝓝 (0:ℂ), complexBranch M p b z (jCpx M p) = 1+z := by
    filter_upwards [hj] with z hz
    change extendComplex (b z) ((1 : ℂ) ⊗ₜ[ℤ] j M p) = _
    rw [extendComplex_tmul,one_mul,hz]
  let a := rationalFrame M p hp hu ω
  have he : pull M p ω = complexify M p a • D ℂ (Cpx M p) (jCpx M p) :=
    (congrArg (pull M p) (regular_coefficient M p hp hu ω)).trans (pull_dj M p a)
  rw [he]
  exact (evaluate_dj (complexBranch M p b) (complexBranch_hol M p b hhol)
    (jCpx M p) (complexify M p a) hj').trans (same_eval_on_rational M p (b 0) a)

end SelectedSameJOneDifferentialEvaluation318

#print axioms SelectedSameJOneDifferentialEvaluation318.pull_dj
#print axioms SelectedSameJOneDifferentialEvaluation318.branch_evaluates_same_coefficient
