module
public import ActualTZCanonicalWrapFibres318
public section
noncomputable section
namespace ActualTZRetainedHorizon318
open ActualTZCanonicalWrapFibres318

theorem residue_range (n : ℕ) (hn : 0<n) (z : ℤ) :
    1≤residue n z ∧ residue n z≤(n:ℤ) := by
  have hN : 0<(n:ℤ) := by exact_mod_cast hn
  unfold residue
  have H₁ := Int.emod_nonneg (z-1) hN.ne'
  have H₂ := Int.emod_lt_of_pos (z-1) hN
  omega

/-- A nonzero literal retained physical difference can only have a
prime divisor within the original 2N horizon. The equality-zero
strip is removed before applying this lemma. -/
theorem horizon (W N n p : ℕ) (hW : 0<W) (hn : 0<n) (hN : W*n≤N)
    (x x' b b' : ℤ) (hB : 1≤b ∧ b≤(W:ℤ)) (hB' : 1≤b' ∧ b'≤(W:ℤ))
    (hNe : (W:ℤ)*residue n x+b-( (W:ℤ)*residue n x'+b')≠0)
    (hD : (p:ℤ)∣(W:ℤ)*residue n x+b-((W:ℤ)*residue n x'+b')) :
    p≤2*N := by
  let U := (W:ℤ)*residue n x+b
  let V := (W:ℤ)*residue n x'+b'
  have hW0 : 0≤(W:ℤ) := by positivity
  have hU : 0≤U ∧ U≤(W:ℤ)*(n:ℤ)+(W:ℤ) := by
    constructor
    · exact add_nonneg (mul_nonneg hW0 (zero_le_one.trans (residue_range n hn x).1))
        (zero_le_one.trans hB.1)
    · exact add_le_add (mul_le_mul_of_nonneg_left (residue_range n hn x).2 hW0) hB.2
  have hV : 0≤V ∧ V≤(W:ℤ)*(n:ℤ)+(W:ℤ) := by
    constructor
    · exact add_nonneg (mul_nonneg hW0 (zero_le_one.trans (residue_range n hn x').1))
        (zero_le_one.trans hB'.1)
    · exact add_le_add (mul_le_mul_of_nonneg_left (residue_range n hn x').2 hW0) hB'.2
  have H : |U-V|≤(2*(N:ℤ)) := by
    apply abs_le.mpr
    have hWN : (W:ℤ)*(n:ℤ)≤(N:ℤ) := by exact_mod_cast hN
    have hn1 : (1:ℤ)≤(n:ℤ) := by exact_mod_cast (show 1≤n by omega)
    have hW' : (W:ℤ)≤(W:ℤ)*(n:ℤ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 hW0
    constructor <;> linarith only [hU.1,hU.2,hV.1,hV.2,hWN,hW']
  have hDiv : p∣(U-V).natAbs := by
    rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
    exact hD
  have hAbs : (U-V).natAbs≤2*N := by
    rw [←Int.natCast_natAbs] at H
    exact_mod_cast H
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hNe) hDiv).trans hAbs

end ActualTZRetainedHorizon318
