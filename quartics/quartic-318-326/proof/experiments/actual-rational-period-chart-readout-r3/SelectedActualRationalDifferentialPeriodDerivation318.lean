module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic.Ring

public section

noncomputable section

namespace SelectedActualRationalDifferentialPeriodDerivation318

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The analytically differentiable evaluations at the chosen period form a
rational subalgebra. No holomorphicity assertion for an entire normalized
coordinate ring is needed, only its actual generators. -/
def differentiableEval (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ) : Subalgebra ℚ A where
  carrier := {a : A | DifferentiableAt ℂ (fun z => e z a) τ}
  zero_mem' := by
    change DifferentiableAt ℂ (fun z => e z 0) τ
    simp only [map_zero]
    exact differentiableAt_const 0
  one_mem' := by
    change DifferentiableAt ℂ (fun z => e z 1) τ
    simp only [map_one]
    exact differentiableAt_const 1
  add_mem' {a b} ha hb := by
    change DifferentiableAt ℂ (fun z => e z (a + b)) τ
    have he : (fun z : ℂ => e z (a + b)) = (fun z : ℂ => e z a + e z b) :=
      funext (fun z => (e z).map_add a b)
    rw [he]
    exact DifferentiableAt.fun_add ha hb
  mul_mem' {a b} ha hb := by
    change DifferentiableAt ℂ (fun z => e z (a * b)) τ
    have he : (fun z : ℂ => e z (a * b)) = (fun z : ℂ => e z a * e z b) :=
      funext (fun z => (e z).map_mul a b)
    rw [he]
    exact DifferentiableAt.fun_mul ha hb
  algebraMap_mem' r := by
    change DifferentiableAt ℂ (fun z => e z (algebraMap ℚ A r)) τ
    simp only [AlgHom.commutes]
    exact differentiableAt_const (algebraMap ℚ ℂ r)

theorem differentiable_of_period_generators
    (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ) (S : Set A)
    (hS : Algebra.adjoin ℚ S = ⊤)
    (h : ∀ a ∈ S, DifferentiableAt ℂ (fun z => e z a) τ) (a : A) :
    DifferentiableAt ℂ (fun z => e z a) τ := by
  have he : Algebra.adjoin ℚ S ≤ differentiableEval e τ := Algebra.adjoin_le h
  exact he (show a ∈ Algebra.adjoin ℚ S from hS.symm ▸ (show a ∈ (⊤ : Subalgebra ℚ A) from trivial))

/-- Differentiate actual period evaluations in the scalar module at the
same center; the usual product rule constructs the true Kähler derivation. -/
def evaluationDerivation (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ)
    (h : ∀ a, DifferentiableAt ℂ (fun z => e z a) τ) :
    letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
    Derivation ℚ A ℂ := by
  letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
  exact {
    toLinearMap := {
      toFun a := deriv (fun z => e z a) τ
      map_add' a b := by
        simp only [map_add]
        exact deriv_fun_add (h a) (h b)
      map_smul' r a := by
        simp only [Algebra.smul_def, map_mul, AlgHom.commutes, RingHom.id_apply]
        exact deriv_const_mul _ (h a) }
    map_one_eq_zero' := by
      change deriv (fun z => e z 1) τ = 0
      simp only [map_one, deriv_const]
    leibniz' a b := by
      change deriv (fun z => e z (a * b)) τ =
        e τ a * deriv (fun z => e z b) τ + e τ b * deriv (fun z => e z a) τ
      simp only [map_mul]
      rw [deriv_fun_mul (h a) (h b)]
      ring }

theorem evaluationDerivation_apply (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ)
    (h : ∀ a, DifferentiableAt ℂ (fun z => e z a) τ) (a : A) :
    letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
    evaluationDerivation e τ h a = deriv (fun z => e z a) τ := by
  unfold evaluationDerivation
  rfl

/-- Exact period coefficient of the normalized dJ frame.
The h frame below is the actual normalized ordinary frame, not an
independently prescribed analytic differential. The right side is an
evaluation in the literal algebra times the derivative of its literal J. -/
theorem pullback_normalized_differential
    (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ)
    (h : ∀ a, DifferentiableAt ℂ (fun z => e z a) τ)
    (J : A) (frame : KaehlerDifferential ℚ A ≃ₗ[A] A)
    (hJ : frame (KaehlerDifferential.D ℚ A J) = 1)
    (ω : KaehlerDifferential ℚ A) :
    letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
    letI : IsScalarTower ℚ A ℂ :=
      IsScalarTower.of_algebraMap_eq (fun r => ((e τ).commutes r).symm)
    (evaluationDerivation e τ h).liftKaehlerDifferential ω =
      e τ (frame ω) * deriv (fun z => e z J) τ := by
  letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
  letI : IsScalarTower ℚ A ℂ :=
    IsScalarTower.of_algebraMap_eq (fun r => ((e τ).commutes r).symm)
  let δ : Derivation ℚ A ℂ := evaluationDerivation e τ h
  have hω : ω = (frame ω) • KaehlerDifferential.D ℚ A J := by
    apply frame.injective
    rw [map_smul, hJ, smul_eq_mul, mul_one]
  change δ.liftKaehlerDifferential ω = _
  calc
    δ.liftKaehlerDifferential ω =
        δ.liftKaehlerDifferential ((frame ω) • KaehlerDifferential.D ℚ A J) :=
      congrArg δ.liftKaehlerDifferential hω
    _ = (frame ω) • δ J := by rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]
    _ = e τ (frame ω) * deriv (fun z => e z J) τ := by
      rw [Algebra.smul_def]
      exact congrArg (fun z : ℂ => e τ (frame ω) * z) (evaluationDerivation_apply e τ h J)

/-- The same differential evaluated along the actual period germ can be formed
from a generating set rather than an assumed differentiable family on all
elements. The expected actual generators are J, the inverse denominator,
and the chosen monogenic root. -/
theorem pullback_normalized_differential_of_generators
    (e : ℂ → A →ₐ[ℚ] ℂ) (τ : ℂ) (S : Set A)
    (hS : Algebra.adjoin ℚ S = ⊤)
    (h : ∀ a ∈ S, DifferentiableAt ℂ (fun z => e z a) τ)
    (J : A) (frame : KaehlerDifferential ℚ A ≃ₗ[A] A)
    (hJ : frame (KaehlerDifferential.D ℚ A J) = 1)
    (ω : KaehlerDifferential ℚ A) :
    letI : Algebra A ℂ := (e τ).toRingHom.toAlgebra
    letI : IsScalarTower ℚ A ℂ :=
      IsScalarTower.of_algebraMap_eq (fun r => ((e τ).commutes r).symm)
    (evaluationDerivation e τ (differentiable_of_period_generators e τ S hS h)).liftKaehlerDifferential ω =
      e τ (frame ω) * deriv (fun z => e z J) τ :=
  pullback_normalized_differential e τ (differentiable_of_period_generators e τ S hS h) J frame hJ ω

end SelectedActualRationalDifferentialPeriodDerivation318

#print axioms SelectedActualRationalDifferentialPeriodDerivation318.pullback_normalized_differential_of_generators
