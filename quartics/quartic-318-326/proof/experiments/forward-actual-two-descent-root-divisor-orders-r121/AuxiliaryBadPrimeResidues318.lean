module
public import LegendrePadicPrimitiveResidues318
public import LegendrePrimitiveModularRoot318
public import LegendreSharedPrimeResidue318
public section
namespace AuxiliaryBadPrimeResidues318

private theorem six_mul_unit (p : ℕ) [Fact p.Prime] (D : ℤ)
    (h6 : ¬(p:ℤ)∣6) (hD : ¬(p:ℤ)∣D) : ¬(p:ℤ)∣6*D := by
  have h6z : (6:ZMod p)≠0 := by
    intro h
    exact h6 ((ZMod.intCast_zmod_eq_zero_iff_dvd 6 p).mp (by simpa using h))
  have hDz : (D:ZMod p)≠0 := fun h =>
    hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (6*D) p).mpr hd
  exact (mul_ne_zero h6z hDz) (by simpa only [Int.cast_mul,Int.cast_ofNat] using hz)

/-- At a prime occurring exactly once in C and also in the selected value,
the actual B-side supplies the positive residual ratio E/D as a square.
No integral coordinates or primitive residue vector are assumed. E may be a
nonunit here; its nonzero condition for Jacobi conversion is separate. -/
theorem selected_ratio (p : ℕ) [Fact p.Prime] (D E : ℤ)
    (h6 : ¬(p:ℤ)∣6) (hD : ¬(p:ℤ)∣D)
    (T Y : ℚ_[p])
    (hB : (((p:ℤ)*D:ℤ):ℚ_[p])*T^2-6*Y^2=(((p:ℤ)*E:ℤ):ℚ_[p])) :
    IsSquare ((E:ZMod p)/(D:ZMod p)) := by
  have hlocal : (6*Y)^2-(((p:ℤ)*(6*D):ℤ):ℚ_[p])*T^2=
      (((p:ℤ)*(-6*E):ℤ):ℚ_[p]) := by
    push_cast at hB ⊢
    linear_combination -6*hB
  obtain ⟨X,Z,W,hcong,hprim⟩ := LegendrePadicPrimitiveResidues318.residues_of_local_solution
    p ((p:ℤ)*(6*D)) ((p:ℤ)*(-6*E)) T (6*Y) 1 (by simp)
    (by simpa only [one_pow,mul_one,sub_eq_zero] using hlocal)
  have hs := LegendreSharedPrimeResidue318.square_ratio_of_primitive_mod_square
    p (6*D) (-6*E) X Z W (six_mul_unit p D h6 hD)
    (by simpa only [mul_assoc] using hcong) hprim
  have h6z : (6:ZMod p)≠0 := by
    intro h
    exact h6 ((ZMod.intCast_zmod_eq_zero_iff_dvd 6 p).mp (by simpa using h))
  have hDz : (D:ZMod p)≠0 := fun h =>
    hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)
  have heq : -((-6*E:ℤ):ZMod p)/((6*D:ℤ):ZMod p)=(E:ZMod p)/(D:ZMod p) := by
    push_cast
    field_simp [h6z,hDz] <;> ring
  rwa [heq] at hs

/-- At a prime occurring exactly once in C, swapping the two homogeneous
coordinates in the transformed B-side gives a square root of -6t modulo p.
This statement does not need t to be a unit; that condition is used only
later when the modular square is converted to Jacobi value1. -/
theorem unselected_square (p : ℕ) [Fact p.Prime] (D t : ℤ)
    (h6 : ¬(p:ℤ)∣6) (hD : ¬(p:ℤ)∣D)
    (T Y : ℚ_[p])
    (hB : (((p:ℤ)*D:ℤ):ℚ_[p])*T^2-6*Y^2=(t:ℚ_[p])) :
    IsSquare ((-6*t:ℤ):ZMod p) := by
  have hlocal : (6*Y)^2-((-6*t:ℤ):ℚ_[p])*(1:ℚ_[p])^2-
      (((p:ℤ)*(6*D):ℤ):ℚ_[p])*T^2=0 := by
    push_cast at hB ⊢
    linear_combination -6*hB
  obtain ⟨X,Z,W,hcong,hprim⟩ := LegendrePadicPrimitiveResidues318.residues_of_local_solution
    p (-6*t) ((p:ℤ)*(6*D)) 1 (6*Y) T (by simp) hlocal
  exact LegendrePrimitiveModularRoot318.square_of_primitive_mod_square
    p (-6*t) (6*D) X Z W (six_mul_unit p D h6 hD) hcong hprim

end AuxiliaryBadPrimeResidues318
