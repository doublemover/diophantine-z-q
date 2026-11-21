module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
open Polynomial
namespace SelectedComplexOrdinaryBase318

@[expose] def denominator : ℂ[X] := X*(X-1728)

abbrev Base := Localization.Away denominator
abbrev Ordinary := {j : ℂ // j ≠ 0 ∧ j ≠ 1728}

@[expose] def jCoord : Base := algebraMap ℂ[X] Base X

@[expose] def polynomialEval (j : Ordinary) : ℂ[X] →+* ℂ :=
  Polynomial.evalRingHom j.val

theorem denominator_unit (j : Ordinary) : IsUnit (polynomialEval j denominator) := by
  apply isUnit_iff_ne_zero.mpr
  simpa [polynomialEval,denominator] using mul_ne_zero j.property.1
    (sub_ne_zero.mpr j.property.2)

@[expose] def evaluation (j : Ordinary) : Base →+* ℂ :=
  IsLocalization.Away.lift denominator (denominator_unit j)

theorem evaluation_polynomial (j : Ordinary) (p : ℂ[X]) :
    evaluation j (algebraMap ℂ[X] Base p) = Polynomial.eval j.val p :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem evaluation_j (j : Ordinary) : evaluation j jCoord = j.val := by
  rw [jCoord,evaluation_polynomial,eval_X]

/-- Every genuine localized coefficient is continuous on the whole
ordinary complex base. The denominator is the SAME localized
polynomial, not an arbitrary continuous coefficient witness. -/
theorem continuous_coefficient (r : Base) :
    Continuous (fun j : Ordinary => evaluation j r) := by
  obtain ⟨⟨f,s⟩,hs⟩ := IsLocalization.surj (Submonoid.powers denominator) r
  have hunit : IsUnit (algebraMap ℂ[X] Base (s : ℂ[X])) :=
    IsLocalization.map_units Base s
  have hn (j : Ordinary) : Polynomial.eval j.val (s : ℂ[X]) ≠ 0 := by
    rw [← evaluation_polynomial]
    exact isUnit_iff_ne_zero.mp (hunit.map (evaluation j))
  have hq (j : Ordinary) :
      evaluation j r = Polynomial.eval j.val f / Polynomial.eval j.val (s : ℂ[X]) := by
    have h := congrArg (evaluation j) hs
    rw [map_mul,evaluation_polynomial,evaluation_polynomial] at h
    exact (eq_div_iff (hn j)).mpr h
  have hc := (f.continuous.comp continuous_subtype_val).div
    ((s : ℂ[X]).continuous.comp continuous_subtype_val) hn
  exact (funext hq).symm ▸ hc

/-- Joint evaluation of any genuine polynomial in the same abscissa
and the complex ordinary coefficients is continuous. -/
theorem continuous_evaluation (p : Base[X]) :
    Continuous (fun z : Ordinary × ℂ => p.eval₂ (evaluation z.1) z.2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he : (fun z : Ordinary × ℂ => (p+q).eval₂ (evaluation z.1) z.2) =
        (fun z : Ordinary × ℂ => p.eval₂ (evaluation z.1) z.2) +
          (fun z : Ordinary × ℂ => q.eval₂ (evaluation z.1) z.2) := by
      funext z
      rw [Pi.add_apply,eval₂_add]
    rw [he]
    exact hp.add hq
  | monomial n a =>
    let c : Ordinary × ℂ → ℂ := (fun j => evaluation j a) ∘ Prod.fst
    let x : Ordinary × ℂ → ℂ := Prod.snd
    have he : (fun z : Ordinary × ℂ => (monomial n a).eval₂ (evaluation z.1) z.2) =
        c * x^n := by
      funext z
      rw [Pi.mul_apply,Pi.pow_apply,eval₂_monomial] <;> rfl
    rw [he]
    exact ((continuous_coefficient a).comp continuous_fst).mul (continuous_snd.pow n)

end SelectedComplexOrdinaryBase318

#print axioms SelectedComplexOrdinaryBase318.continuous_coefficient
#print axioms SelectedComplexOrdinaryBase318.continuous_evaluation
