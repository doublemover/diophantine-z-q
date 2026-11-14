module
public import OriginalFiveKernelDecomposition318
public section
noncomputable section
namespace MultiplicativeRationalEighth318
variable (V : Type) [AddCommGroup V] [Module ℚ V]
/-- Rational characteristic zero gives a UNIQUE eighth root. This lemma
is applied only to actual first-order kernels, never entire Picard groups. -/
@[expose] def equivalence : Multiplicative V ≃* Multiplicative V where
  toFun x := Multiplicative.ofAdd ((8 : ℚ) • x.toAdd)
  invFun x := Multiplicative.ofAdd ((1 / 8 : ℚ) • x.toAdd)
  left_inv x := by change Multiplicative.ofAdd ((1 / 8 : ℚ) • ((8 : ℚ) • x.toAdd)) = x; rw [smul_smul]; norm_num
  right_inv x := by change Multiplicative.ofAdd ((8 : ℚ) • ((1 / 8 : ℚ) • x.toAdd)) = x; rw [smul_smul]; norm_num
  map_mul' x y := by change Multiplicative.ofAdd ((8 : ℚ) • (x.toAdd + y.toAdd)) =
      Multiplicative.ofAdd ((8 : ℚ) • x.toAdd + (8 : ℚ) • y.toAdd); rw [smul_add]
lemma apply_pow (x : Multiplicative V) : equivalence V x = x ^ 8 := by
  change Multiplicative.ofAdd ((8 : ℚ) • x.toAdd) = Multiplicative.ofAdd (8 • x.toAdd)
  rw [Nat.cast_smul_eq_nsmul]
end MultiplicativeRationalEighth318
