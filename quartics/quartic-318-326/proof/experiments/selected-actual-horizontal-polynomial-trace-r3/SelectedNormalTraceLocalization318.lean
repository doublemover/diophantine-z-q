module
public import SelectedTraceDualNormalization318
public import Mathlib.RingTheory.Localization.Integral
public section
noncomputable section

open SelectedTraceDualNormalization318

namespace SelectedNormalTraceLocalization318

variable {A R K F : Type*}
variable [CommRing A] [CommRing R] [Field K] [CommRing F]
variable [Algebra A R]
variable [Algebra A K] [Algebra A F] [Algebra R K] [Algebra R F] [Algebra K F]
variable [IsScalarTower A R K] [IsScalarTower A K F] [IsScalarTower R K F]
variable [IsScalarTower A R F]

/-- A global normal trace-dual element is in the local normal trace
dual on the SAME generic K-algebra. An integral y after localization
is handled by a true denominator s with sy integral before localization;
no trace from a different generic field, and no finite-free hypothesis
on a principal open of the order. -/
theorem global_mem_local (S : Submonoid A) [IsLocalization S R] {x : F}
    (hx : x ∈ complementary K (integralClosure A F)) :
    x ∈ complementary K (integralClosure R F) := by
  apply mem_complementary.mpr
  intro y hy
  have hy' : IsIntegral R y := (mem_integralClosure_iff R F).mp hy
  obtain ⟨s,hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ:=R) S y hy'
  have hs' : s • y ∈ integralClosure A F := (mem_integralClosure_iff A F).mpr hs
  have hc := mem_complementary.mp hx (s • y) hs'
  obtain ⟨c,hc⟩ := Submodule.mem_one.mp hc
  have hc' : Algebra.trace K F (x*(s • y)) ∈ (1 : Submodule R K) :=
    Submodule.mem_one.mpr ⟨algebraMap A R c,
      (IsScalarTower.algebraMap_apply A R K c).symm.trans hc⟩
  have hTr : Algebra.trace K F (x*(s • y)) =
      algebraMap A K (s:A) * Algebra.trace K F (x*y) := by
    have hxy : x*(s • y) = algebraMap A K (s:A) • (x*y) := by
      change x*((s:A) • y) = _
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A K F, Algebra.smul_def]
      ac_rfl
    rw [hxy, map_smul, smul_eq_mul]
  let u : Rˣ := (IsLocalization.map_units R s).unit
  have hu : (u:R) = algebraMap A R (s:A) := (IsLocalization.map_units R s).unit_spec
  have hcancel : ((u⁻¹ : Rˣ):R) * algebraMap A R (s:A) = 1 :=
    (congrArg (fun a : R => ((u⁻¹:Rˣ):R)*a) hu.symm).trans (Units.inv_mul u)
  have hsCancel : ((u⁻¹ : Rˣ):R) • Algebra.trace K F (x*(s • y)) =
      Algebra.trace K F (x*y) := by
    rw [Algebra.smul_def, hTr, IsScalarTower.algebraMap_apply A R K, ←mul_assoc,
      ←map_mul, hcancel, map_one, one_mul]
  exact hsCancel ▸ (1 : Submodule R K).smul_mem ((u⁻¹:Rˣ):R) hc'

/-- In particular, a genuine local clearing result on the normalized
ring applies to the global trace-dual element without a substitute
polynomial equation or change of K. -/
theorem local_integral_of_clear (S : Submonoid A) [IsLocalization S R] {x : F} (hx : x ∈ complementary K (integralClosure A F))
    (M : ℕ) (clear : ∀ y ∈ complementary K (integralClosure R F),
      (M:F)*y ∈ integralClosure R F) :
    IsIntegral R ((M:F)*x) :=
  (mem_integralClosure_iff R F).mp (clear x (global_mem_local S hx))

end SelectedNormalTraceLocalization318

#print axioms SelectedNormalTraceLocalization318.global_mem_local
#print axioms SelectedNormalTraceLocalization318.local_integral_of_clear
