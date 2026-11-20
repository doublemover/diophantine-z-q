module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic
public section
noncomputable section
open Filter Topology

namespace SelectedJOneKaehlerEvaluation318

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Scalar extension at the actual center of the analytic family of algebra
evaluations. The A-action on complex tangent coefficients is through this
point, not through another algebraic point of the ordinary fiber. -/
abbrev pointAlgebra (branch : ℂ → A →ₐ[ℂ] ℂ) : Algebra A ℂ :=
  (branch 0).toRingHom.toAlgebra

/-- Differentiate pullbacks of actual local regular functions. This constructs
the algebraic derivation from the analytic family, without assuming the
differential comparison or importing a global analytification functor. -/
def branchDerivation (branch : ℂ → A →ₐ[ℂ] ℂ)
    (hol : ∀ a, DifferentiableAt ℂ (fun z => branch z a) 0) :
    letI := pointAlgebra branch
    Derivation ℂ A ℂ := by
  letI := pointAlgebra branch
  refine
    { toLinearMap :=
        { toFun := fun a => deriv (fun z => branch z a) 0
          map_add' := ?_
          map_smul' := ?_ }
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · intro a b
    change deriv (fun z => branch z (a+b)) 0 =
      deriv (fun z => branch z a) 0 + deriv (fun z => branch z b) 0
    simpa only [map_add] using ((hol a).hasDerivAt.add (hol b).hasDerivAt).deriv
  · intro r a
    change deriv (fun z => branch z (r • a)) 0 =
      r * deriv (fun z => branch z a) 0
    have he : (fun z => branch z (r • a)) = fun z => r * branch z a := by
      funext z
      simp [Algebra.smul_def]
    rw [he]
    exact ((hol a).hasDerivAt.const_mul r).deriv
  · change deriv (fun z => branch z 1) 0 = 0
    simp
  · intro a b
    change deriv (fun z => branch z (a*b)) 0 =
      branch 0 a * deriv (fun z => branch z b) 0 +
        branch 0 b * deriv (fun z => branch z a) 0
    simp only [map_mul]
    rw [((hol a).hasDerivAt.mul (hol b).hasDerivAt).deriv]
    ring

theorem branch_deriv_apply (branch : ℂ → A →ₐ[ℂ] ℂ)
    (hol : ∀ a, DifferentiableAt ℂ (fun z => branch z a) 0) (a : A) :
    letI := pointAlgebra branch
    branchDerivation branch hol a = deriv (fun z => branch z a) 0 := rfl

/-- At z=0 on the literal centered j-coordinate, the induced linear
map on the algebraic Kähler module sends a·dj to the value of a at
the SAME algebraic point. Thus once the actual finite étale chart gives
θ_j = a_j·dj, there is no additional scalar/chosen trivialization in the
embedded evaluation minor. No CM, genus, or Jacobian assumptions occur. -/
theorem evaluate_dj (branch : ℂ → A →ₐ[ℂ] ℂ)
    (hol : ∀ a, DifferentiableAt ℂ (fun z => branch z a) 0)
    (j a : A) (jChart : ∀ᶠ z : ℂ in 𝓝 0, branch z j = 1+z) :
    letI := pointAlgebra branch
    letI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom (branch 0)
    (branchDerivation branch hol).liftKaehlerDifferential
      (a • KaehlerDifferential.D ℂ A j) = branch 0 a := by
  letI := pointAlgebra branch
  letI : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom (branch 0)
  have hj : HasDerivAt (fun z => branch z j) 1 0 :=
    ((hasDerivAt_id' (0:ℂ)).const_add (1:ℂ)).congr_of_eventuallyEq jChart
  rw [map_smul,Derivation.liftKaehlerDifferential_comp_D,branch_deriv_apply,hj.deriv]
  change branch 0 a * 1 = branch 0 a
  exact mul_one _

end SelectedJOneKaehlerEvaluation318
#print axioms SelectedJOneKaehlerEvaluation318.branch_deriv_apply
#print axioms SelectedJOneKaehlerEvaluation318.evaluate_dj
