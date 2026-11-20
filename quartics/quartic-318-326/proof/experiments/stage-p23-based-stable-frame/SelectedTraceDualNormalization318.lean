module
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public section
noncomputable section
open Polynomial
open scoped Pointwise

namespace SelectedTraceDualNormalization318

section SameTrace
variable {R K F : Type*} [CommRing R] [Field K] [CommRing F]
variable [Algebra R K] [Algebra K F] [Algebra R F] [IsScalarTower R K F]

/-- The actual complementary submodule inside this generic algebra,
with the actual algebra trace to its coefficient field K. -/
abbrev complementary (K : Type*) {R F : Type*} [CommRing R] [Field K] [CommRing F]
    [Algebra R K] [Algebra K F] [Algebra R F] [IsScalarTower R K F]
    (A : Subalgebra R F) : Submodule R F :=
  (Algebra.traceForm K F).dualSubmodule A.toSubmodule

theorem mem_complementary {A : Subalgebra R F} {x : F} :
    x ∈ complementary K A ↔
      ∀ y ∈ A, Algebra.trace K F (x*y) ∈ (1 : Submodule R K) := by
  simpa only [Algebra.traceForm_apply,Subalgebra.mem_toSubmodule] using
    (LinearMap.BilinForm.mem_dualSubmodule (Algebra.traceForm K F)
      (N := A.toSubmodule) (x := x))

/-- No change of trace, no ramification quotient or residue-field
separability hypothesis enters this integral inclusion. -/
theorem complementary_anti {A B : Subalgebra R F} (h : A ≤ B) :
    complementary K B ≤ complementary K A := by
  intro x hx
  exact mem_complementary.mpr (fun y hy => mem_complementary.mp hx y (h hy))

/-- More strongly, the same coefficient sends B's trace dual into A.
The last inclusion into B is only the original integral inclusion. -/
theorem clear_overorder {A B : Subalgebra R F} (h : A ≤ B) (a : F)
    (clear : ∀ x ∈ complementary K A, a*x ∈ A) :
    ∀ x ∈ complementary K B, a*x ∈ A :=
  fun x hx => clear x (complementary_anti h hx)

end SameTrace

section SingleGenericField
variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

/-- Use the same integral root equation and its actual derivative, not
a newly chosen primitive element or its monic equation in another field. -/
theorem monogenic_clear
    {x : F} (hx : Algebra.adjoin K ({x} : Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (a : R) {w : F} (hw : w ∈ Algebra.adjoin R ({x} : Set F))
    (witness : aeval x p.derivative * w = algebraMap R F a) :
    ∀ z ∈ complementary K (Algebra.adjoin R ({x} : Set F)),
      algebraMap R F a * z ∈ Algebra.adjoin R ({x} : Set F) := by
  let d : F := aeval x (minpoly K x).derivative
  have hd : d ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K x).aeval_derivative_ne_zero (minpoly.aeval K x)
  have hdp : d = aeval x p.derivative := by
    change aeval x (minpoly K x).derivative = _
    rw [←hp,derivative_map,aeval_map_algebraMap]
  have ha : d*w = algebraMap R F a := by rw [hdp,witness]
  intro z hz
  have hz' : z ∈ d⁻¹ • (Algebra.adjoin R ({x} : Set F)).toSubmodule := by
    change z ∈ (Algebra.traceForm K F).dualSubmodule
      (Algebra.adjoin R ({x} : Set F)).toSubmodule at hz
    rw [traceForm_dualSubmodule_adjoin R K hx hint] at hz
    exact hz
  obtain ⟨y,hy,hyz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz'
  have he : algebraMap R F a * z = w*y := by
    change d⁻¹ * y = z at hyz
    rw [←ha,←hyz]
    calc
      (d*w)*(d⁻¹*y) = (d*d⁻¹)*(w*y) := by ac_rfl
      _ = w*y := by rw [mul_inv_cancel₀ hd,one_mul]
  rw [he]
  exact mul_mem hw (Subalgebra.mem_toSubmodule.mp hy)

/-- On the actual integral closure in this same generic field, the
literal integer M clears the trace-dual, and even lands back in the
given monogenic order. This is before any regular-resolution or stable
Hodge lattice comparison. -/
theorem actual_normalization_clear
    {x : F} (hx : Algebra.adjoin K ({x} : Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (M : ℕ) {w : F} (hw : w ∈ Algebra.adjoin R ({x} : Set F))
    (witness : aeval x p.derivative * w = (M:F)) :
    ∀ z ∈ complementary K (integralClosure R F),
      (M:F)*z ∈ Algebra.adjoin R ({x} : Set F) ∧ (M:F)*z ∈ integralClosure R F := by
  have hA : Algebra.adjoin R ({x} : Set F) ≤ integralClosure R F := by
    apply Algebra.adjoin_le
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact mem_integralClosure_iff.mpr hint
  have hclear := monogenic_clear hx hint p hp (M:R) hw
    (by simpa only [map_natCast] using witness)
  intro z hz
  have hz' : (M:F)*z ∈ Algebra.adjoin R ({x} : Set F) := by
    simpa only [map_natCast] using
      (clear_overorder (K:=K) hA (algebraMap R F (M:R)) hclear z hz)
  exact ⟨hz',hA hz'⟩

end SingleGenericField
end SelectedTraceDualNormalization318

#print axioms SelectedTraceDualNormalization318.complementary_anti
#print axioms SelectedTraceDualNormalization318.clear_overorder
#print axioms SelectedTraceDualNormalization318.monogenic_clear
#print axioms SelectedTraceDualNormalization318.actual_normalization_clear
