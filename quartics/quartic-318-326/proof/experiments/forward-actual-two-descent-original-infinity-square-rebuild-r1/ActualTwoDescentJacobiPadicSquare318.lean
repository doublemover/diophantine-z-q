module
public import ActualTwoDescentHenselSquare318
public section
noncomputable section
namespace ActualTwoDescentJacobiPadicSquare318
open ActualTwoDescentHenselSquare318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- A unit with actual Jacobi symbol1 has an actual root in Q_p, via a
finite-field root, its literal integer representative, and Hensel lifting. -/
theorem actual_jacobi_padic_square (hp2 : p ≠ 2) (A : ℕ)
    (hA : Nat.Coprime A p) (hJ : jacobiSym (A : ℤ) p=1) :
    ∃ r : ℚ_[p], r^2=(A : ℚ_[p]) := by
  obtain ⟨z,hz⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  have hunit : IsUnit (A : ZMod p) := (ZMod.isUnit_iff_coprime A p).mpr hA
  have hz0 : z ≠ 0 := by
    intro he
    apply hunit.ne_zero
    simpa only [he,mul_zero,Int.cast_natCast] using hz
  have hx : Nat.Coprime p z.val := by
    apply Nat.Coprime.symm
    apply (ZMod.isUnit_iff_coprime z.val p).mp
    rw [ZMod.natCast_zmod_val]
    exact isUnit_iff_ne_zero.mpr hz0
  have he : (((z.val : ℤ)^2-A : ℤ) : ZMod p)=0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    have hzz : (A : ZMod p)=z*z := by simpa only [Int.cast_natCast] using hz
    rw [hzz]
    ring
  have hdiv : (p : ℤ) ∣ (z.val : ℤ)^2-A :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he
  obtain ⟨r,hr⟩ := actual_odd_square_lift hp2 A z.val hx hdiv
  refine ⟨(r : ℚ_[p]),?_⟩
  exact_mod_cast hr

/-- The lifted root is nonzero whenever the original integer is nonzero.
This retains the units required by Kummer squareclass comparisons. -/
theorem actual_jacobi_padic_unit_square (hp2 : p ≠ 2) (A : ℕ)
    (hA0 : A ≠ 0) (hA : Nat.Coprime A p) (hJ : jacobiSym (A : ℤ) p=1) :
    ∃ r : ℚ_[p], r ≠ 0 ∧ r^2=(A : ℚ_[p]) := by
  obtain ⟨r,hr⟩ := actual_jacobi_padic_square hp2 A hA hJ
  refine ⟨r,?_,hr⟩
  intro he
  have h := hr
  rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  exact (Nat.cast_ne_zero.mpr hA0) h.symm

end ActualTwoDescentJacobiPadicSquare318
