module
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace LenstraTrace318
open Module Algebra

variable (A K L:Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [CharZero K]

/-- The reciprocal of a nonzero nonunit does not lie in the original
integral domain inside its actual fraction field. -/
theorem inverse_not_in_base (x:A) (hx:x≠0) (hunit:¬IsUnit x) :
    (algebraMap A K x)⁻¹ ∉ (algebraMap A K).range := by
  rintro ⟨y,hy⟩
  apply hunit
  apply isUnit_iff_exists_inv.mpr
  refine ⟨y,?_⟩
  apply IsFractionRing.injective A K
  rw [map_mul,map_one,hy,mul_inv_cancel₀]
  exact (map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hx

/-- The actual field trace of1/(n x), where n=[L:K], is1/x. -/
theorem trace_inverse_degree (x:K) (hx:x≠0) :
    Algebra.trace K L (algebraMap K L (((Module.finrank K L:K)*x)⁻¹))=x⁻¹ := by
  rw [Algebra.trace_algebraMap,nsmul_eq_mul]
  have hn:(Module.finrank K L:K)≠0 := by
    exact_mod_cast (Module.finrank_pos (R:=K) (M:=L)).ne'
  field_simp

/-- Lenstra's trace obstruction, with the actual field extension and trace. -/
theorem trace_inverse_degree_not_in_base (x:A) (hx:x≠0) (hunit:¬IsUnit x) :
    Algebra.trace K L (algebraMap K L
      (((Module.finrank K L:K)*algebraMap A K x)⁻¹)) ∉ (algebraMap A K).range := by
  rw [trace_inverse_degree K L _ ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hx)]
  exact inverse_not_in_base A K x hx hunit

/-- In particular the reciprocal1/(n x) is excluded from the actual trace
dual of any integral B-algebra unit module. -/
theorem inverse_degree_not_mem_traceDual_one (B:Type*) [CommRing B]
    [Algebra B L] [Algebra A B] [IsScalarTower A B L]
    (x:A) (hx:x≠0) (hunit:¬IsUnit x) :
    algebraMap K L (((Module.finrank K L:K)*algebraMap A K x)⁻¹) ∉
      Submodule.traceDual A K (1:Submodule B L) := by
  intro h
  have hh:Algebra.trace K L (algebraMap K L
      (((Module.finrank K L:K)*algebraMap A K x)⁻¹)) ∈ (algebraMap A K).range := by
    have h1 := (Submodule.mem_traceDual.mp h) 1 (by rw [Submodule.mem_one]; exact ⟨1,map_one _⟩)
    simpa only [Algebra.traceForm_apply,mul_one] using h1
  exact trace_inverse_degree_not_in_base A K L x hx hunit hh

end LenstraTrace318
