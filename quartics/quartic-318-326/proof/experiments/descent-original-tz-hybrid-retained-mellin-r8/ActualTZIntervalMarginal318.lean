module
public import ActualTZResidueIntervalCount318
public section
noncomputable section
namespace ActualTZIntervalMarginal318
open ActualTZResidueIntervalCount318

/-- A single actual signed interval has each residue atom bounded by
1/p+1/L. This works for intervals shorter than p and for negative starts. -/
theorem marginal_le (p L : ℕ) (s r : ℤ) (hp : 0<p) (hL : 0<L) :
    (intHits p L s r:ℝ)/(L:ℝ) ≤ 1/(p:ℝ)+1/(L:ℝ) := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hL' : (0:ℝ)<L := by exact_mod_cast hL
  have h := (abs_le.mp (int_count_error p L s r hp)).2
  apply (div_le_iff₀ hL').2
  have he : (1/(p:ℝ)+1/(L:ℝ))*(L:ℝ)=(L:ℝ)/(p:ℝ)+1 := by
    field_simp [hp'.ne',hL'.ne'] <;> ring
  rw [he]
  linarith

end ActualTZIntervalMarginal318
