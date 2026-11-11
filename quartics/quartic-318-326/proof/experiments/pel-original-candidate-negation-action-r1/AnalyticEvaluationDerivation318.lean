module
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Data.Complex.Basic
public section
noncomputable section
namespace AnalyticEvaluationDerivation318
variable {A V : Type*} [CommRing A] [Algebra ℂ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
/-- Derivations into the residue values at the SPECIFIED algebra point.
The A action is actual evaluation at that point. -/
@[expose] abbrev PointDerivations (e : A →ₐ[ℂ] ℂ) : Type _ :=
  letI : Module A ℂ := Module.compHom ℂ e.toRingHom
  Derivation ℂ A ℂ
variable (ev : V → A →ₐ[ℂ] ℂ) (x : V)
  (hd : ∀ a : A, DifferentiableAt ℂ (fun y => ev y a) x)
  (e : A →ₐ[ℂ] ℂ) (he : ev x = e)
/-- A genuine analytic tangent direction differentiates EVERY element
of the actual algebra, with its original point-evaluation module action. -/
@[expose] def direction (v : V) : PointDerivations e := {
  toFun a := fderiv ℂ (fun y => ev y a) x v
  map_add' a b := by
    simp only [map_add]
    rw [fderiv_fun_add (hd a) (hd b)]
    rfl
  map_smul' c a := by
    simp only [map_smul]
    rw [fderiv_fun_const_smul (hd a) c]
    rfl
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change fderiv ℂ (fun y => ev y (a*b)) x v =
      e a * fderiv ℂ (fun y => ev y b) x v +
      e b * fderiv ℂ (fun y => ev y a) x v
    rw [←he]
    simp only [map_mul]
    rw [fderiv_fun_mul (hd a) (hd b)]
    rfl }
lemma direction_apply (v : V) (a : A) : direction ev x hd e he v a =
    fderiv ℂ (fun y => ev y a) x v := rfl
lemma direction_add (v w : V) (a : A) :
    direction ev x hd e he (v+w) a = direction ev x hd e he v a + direction ev x hd e he w a :=
  map_add _ _ _
lemma direction_smul (c : ℂ) (v : V) (a : A) :
    direction ev x hd e he (c • v) a = c * direction ev x hd e he v a :=
  map_smul _ _ _
end AnalyticEvaluationDerivation318
