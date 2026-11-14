module
public import PELRamifiedPrimitiveCongruence318
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.Finset.Max
public section
noncomputable section
namespace PELPadicCoordinateAnisotropy318
open PELRamifiedPrimitiveCongruence318 PELPrimeNormalizerData318
set_option maxHeartbeats 1800000

/-- Normalize the ACTUAL four p-adic coordinates by a largest-norm one.
This constructs an integral vector containing1; no local division-algebra
classification or anisotropy assumption enters the normalization. -/
theorem anisotropic (i : Fin 4) (a : Fin 4 → ℚ_[prime i]) (ha : a≠0) : polynomial a≠0 := by
  intro hzero
  obtain ⟨j,hjmem,hmax⟩ := Finset.exists_max_image Finset.univ (fun k : Fin 4 => ‖a k‖)
    (show (Finset.univ : Finset (Fin 4)).Nonempty from Finset.univ_nonempty)
  have hj : a j≠0 := by
    intro hz
    apply ha
    funext k
    apply norm_eq_zero.mp
    have hh := hmax k (Finset.mem_univ k)
    rw [hz,norm_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  have hnorm : 0<‖a j‖ := norm_pos_iff.mpr hj
  have hbound (k : Fin 4) : ‖a k/a j‖≤1 := by
    rw [norm_div]
    exact (div_le_one hnorm).mpr (hmax k (Finset.mem_univ k))
  let b : Fin 4 → ℤ_[prime i] := fun k => ⟨a k/a j,hbound k⟩
  have hb1 : b j=1 := by
    apply Subtype.ext
    change a j/a j=1
    exact div_self hj
  have hbQ : polynomial (fun k => a k/a j)=0 := by
    have hh := polynomial_scale (a j)⁻¹ a
    have he : polynomial (fun k => a k/a j)=(a j)⁻¹^2*polynomial a := by
      simpa only [div_eq_mul_inv,mul_comm] using hh
    rw [he,hzero,mul_zero]
  have hb : polynomial b=0 := by
    apply PadicInt.coe_inj.mp
    change ((polynomial b:ℤ_[prime i]):ℚ_[prime i])=0
    exact (polynomial_map (PadicInt.subring (prime i)).subtype b).trans hbQ
  exact zero_has_no_one i (PadicInt.toZModPow 2) b hb j hb1

theorem norm_zero_iff (i : Fin 4) (a : Fin 4 → ℚ_[prime i]) : polynomial a=0 ↔ a=0 := by
  constructor
  · intro h
    by_contra ha
    exact anisotropic i a ha h
  · rintro rfl
    simp [polynomial]
end PELPadicCoordinateAnisotropy318
