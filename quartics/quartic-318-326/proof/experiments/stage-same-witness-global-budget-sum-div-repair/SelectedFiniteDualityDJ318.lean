module
public import SelectedNormalizationDualFunctional318
public section
noncomputable section
open Polynomial SelectedNormalizationDualFunctional318

namespace SelectedFiniteDualityDJ318

variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
local notation "B" => integralClosure R F
local notation "C" => normalizedComplementary (R:=R) (F:=F) K

/-- The actual generic element 1 belongs to the complementary module.
This pins the normalization and gives a spanning test without assuming
that the integral relative dualizing module is free. -/
theorem one_mem_actual_dual : (1:F) ∈ C := by
  apply Submodule.mem_traceDual.mpr
  intro y hy
  obtain ⟨b,hb⟩ := Submodule.mem_one.mp hy
  have hyI : IsIntegral R y := by
    have h : IsIntegral R (b:F) := mem_integralClosure_iff.mp b.2
    have hb' : (b:F) = y := hb
    exact hb' ▸ h
  have H : IsIntegral R (Algebra.trace K F y) := Algebra.isIntegral_trace hyI
  rw [Algebra.traceForm_apply,one_mul]
  exact IsIntegrallyClosed.algebraMap_eq_of_integral H

section Compare
variable {W V : Type*} [AddCommGroup W] [Module B W]
variable [AddCommGroup V] [Module F V] [Module B V]

/-- Transport a genuine finite-duality comparison. On the generic line
the functional is M times the dual of the actual normalized dj frame,
and it is unique with that restriction. No scalar is chosen by the proof. -/
theorem consume_comparison
    (M : ℕ) (c : C →ₗ[B] B) (hc : ∀ z : C, (c z:F) = (M:F)*(z:F))
    (cmp : C ≃ₗ[B] W) (generic : W →ₗ[B] V)
    (frame : F ≃ₗ[F] V) (dj : V) (hdj : frame 1 = dj)
    (same : ∀ z : C, generic (cmp z) = frame (z:F)) :
    ∃ f : W →ₗ[B] B,
      (∀ w : W, ((M:F) • frame.symm.toLinearMap) (generic w) = (f w:F)) ∧
      ((M:F) • frame.symm.toLinearMap) dj = (M:F) ∧
      ∀ g : V →ₗ[F] F, (∀ w : W, g (generic w) = (f w:F)) →
        g = (M:F) • frame.symm.toLinearMap := by
  let f : W →ₗ[B] B := c.comp cmp.symm.toLinearMap
  have hf (z : C) : (f (cmp z):F) = (M:F)*(z:F) := by
    change (c (cmp.symm (cmp z)):F) = _
    rw [cmp.symm_apply_apply,hc]
  refine ⟨f,?_,?_,?_⟩
  · intro w
    obtain ⟨z,rfl⟩ := cmp.surjective w
    rw [same]
    change (M:F)*frame.symm (frame (z:F)) = _
    rw [frame.symm_apply_apply,hf]
  · change (M:F)*frame.symm dj = _
    rw [←hdj,frame.symm_apply_apply,mul_one]
  · intro g hg
    let z : C := ⟨1,one_mem_actual_dual⟩
    have hs : generic (cmp z) = dj := (same z).trans hdj
    have hg_one : g dj = (M:F) := by
      rw [←hs,hg,hf]
      change (M:F)*1 = _
      exact mul_one _
    ext v
    have hv : v = frame.symm v • dj := by
      calc
        v = frame (frame.symm v) := (frame.apply_symm_apply v).symm
        _ = frame (frame.symm v • (1:F)) := by rw [smul_eq_mul,mul_one]
        _ = frame.symm v • dj := by rw [map_smul,hdj]
    change g v = (M:F)*frame.symm v
    conv_lhs => rw [hv]
    rw [map_smul,hg_one,smul_eq_mul,mul_comm]

/-- The actual normalization functional from the monogenic witness,
applied to the supplied finite duality on the same generic field.
The terminal is an affine module statement, not resolution extension. -/
theorem literal_generic_section
    {x : F} (hx : Algebra.adjoin K ({x} : Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (M : ℕ) {w : F} (hw : w ∈ Algebra.adjoin R ({x} : Set F))
    (witness : aeval x p.derivative * w = (M:F))
    (cmp : C ≃ₗ[B] W) (generic : W →ₗ[B] V)
    (frame : F ≃ₗ[F] V) (dj : V) (hdj : frame 1 = dj)
    (same : ∀ z : C, generic (cmp z) = frame (z:F)) :
    ∃ f : W →ₗ[B] B,
      (∀ y : W, ((M:F) • frame.symm.toLinearMap) (generic y) = (f y:F)) ∧
      ((M:F) • frame.symm.toLinearMap) dj = (M:F) ∧
      ∀ g : V →ₗ[F] F, (∀ y : W, g (generic y) = (f y:F)) →
        g = (M:F) • frame.symm.toLinearMap := by
  obtain ⟨f,hf⟩ := literal_dual_functional hx hint p hp M hw witness
  exact consume_comparison M f hf cmp generic frame dj hdj same

end Compare
end SelectedFiniteDualityDJ318

#print axioms SelectedFiniteDualityDJ318.one_mem_actual_dual
#print axioms SelectedFiniteDualityDJ318.consume_comparison
#print axioms SelectedFiniteDualityDJ318.literal_generic_section
