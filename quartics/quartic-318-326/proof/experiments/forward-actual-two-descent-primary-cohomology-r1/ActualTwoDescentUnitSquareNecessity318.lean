module
public import ActualTwoDescentSameExceptionalImages318
public section
noncomputable section
namespace ActualTwoDescentUnitSquareNecessity318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- An actual p-adic square root of an integral unit descends through the
ACTUAL residue map and forces Jacobi symbol1. -/
theorem actual_unit_square_symbol (A : ℤ) (hA : IsCoprime A (p : ℤ))
    (r : ℚ_[p]) (hr : r^2=(A : ℚ_[p])) : jacobiSym A p=1 := by
  have hn : ‖(A : ℚ_[p])‖=1 := Padic.norm_intCast_eq_one_iff.mpr hA
  have hrn : ‖r‖=1 := by
    have h := congrArg norm hr
    rw [norm_pow,hn] at h
    nlinarith [norm_nonneg r]
  let R : ℤ_[p] := ⟨r,hrn.le⟩
  have he : R^2=(A : ℤ_[p]) := by
    apply Subtype.ext
    exact hr
  have hm := congrArg PadicInt.toZMod he
  simp only [map_pow,map_intCast] at hm
  have hs : IsSquare (A : ZMod p) := ⟨PadicInt.toZMod R,by simpa only [pow_two] using hm.symm⟩
  have hg : A.gcd p=1 := Int.isCoprime_iff_gcd_eq_one.mp hA
  rcases jacobiSym.eq_one_or_neg_one hg with h | h
  · exact h
  · exact False.elim ((ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp h) hs)

/-- Integral unit representatives related by an ACTUAL local square have
the same quadratic-residue symbol, including signed representatives. -/
theorem actual_unit_square_comparison (A D : ℤ)
    (hA : IsCoprime A (p : ℤ)) (hD : IsCoprime D (p : ℤ))
    (r : ℚ_[p]) (he : (A : ℚ_[p])=(D : ℚ_[p])*r^2) :
    jacobiSym A p=jacobiSym D p := by
  have hroot : ((D : ℚ_[p])*r)^2=((A*D : ℤ) : ℚ_[p]) := by
    push_cast
    rw [he]
    ring
  have hs := actual_unit_square_symbol (A*D) (hA.mul_left hD) _ hroot
  rw [jacobiSym.mul_left] at hs
  have hgA : A.gcd p=1 := Int.isCoprime_iff_gcd_eq_one.mp hA
  have hgD : D.gcd p=1 := Int.isCoprime_iff_gcd_eq_one.mp hD
  rcases jacobiSym.eq_one_or_neg_one hgA with ha | ha <;>
    rcases jacobiSym.eq_one_or_neg_one hgD with hd | hd <;> rw [ha,hd] at hs ⊢ <;> norm_num at hs ⊢

end ActualTwoDescentUnitSquareNecessity318
