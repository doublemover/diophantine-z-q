module
public import AnalyticEvaluationDerivation318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public section
noncomputable section
namespace EvaluationDualNumberLift318
open AnalyticEvaluationDerivation318
variable {A : Type*} [CommRing A] [Algebra ℂ A]
abbrev Dual := TrivSqZeroExt ℂ ℂ
variable (e : A →ₐ[ℂ] ℂ) (d : PointDerivations e)
/-- The ACTUAL dual-number algebra map encoding a derivation at the
specified original complex point. Constant term is e; epsilon term is d. -/
@[expose] def lift : A →ₐ[ℂ] Dual where
  toFun a := ⟨e a,d a⟩
  map_zero' := TrivSqZeroExt.ext (map_zero e) (map_zero d)
  map_add' a b := TrivSqZeroExt.ext (map_add e a b) (map_add d a b)
  map_one' := TrivSqZeroExt.ext (map_one e) d.map_one_eq_zero
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul e a b
    · change d (a*b) = e a * d b + d a * e b
      have h := d.leibniz a b
      change d (a*b) = e a * d b + e b * d a at h
      simpa only [mul_comm] using h
  commutes' c := TrivSqZeroExt.ext (e.commutes c) (d.map_algebraMap c)
lemma constant_term : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (lift e d) = e := by
  ext a
  rfl
lemma epsilon_term (a : A) : (lift e d a).snd = d a := rfl
theorem lift_injective : Function.Injective (lift e) := by
  intro d₁ d₂ h
  ext a
  exact congrArg (fun f : A →ₐ[ℂ] Dual => (f a).snd) h
end EvaluationDualNumberLift318
