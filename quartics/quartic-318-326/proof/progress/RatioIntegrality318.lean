module
public import FormalLogDepth318
public section
namespace RatioIntegrality318
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime]

theorem integer_nonnegative (n:ℤ) : 0≤Padic.addValuation (n:ℚ_[p]) := by
  by_cases hn:n=0
  · simp [hn]
  rw [Padic.addValuation.apply (Int.cast_ne_zero.mpr hn),Padic.valuation_intCast]
  exact_mod_cast (show (0:ℤ)≤(padicValInt p n:ℤ) by positivity)

theorem neighboring_unit (n:ℤ) :
    Padic.addValuation (n:ℚ_[p])=0 ∨ Padic.addValuation ((n-1:ℤ):ℚ_[p])=0 := by
  by_cases hn:Padic.addValuation (n:ℚ_[p])=0
  · exact Or.inl hn
  right
  have hp:0<Padic.addValuation (n:ℚ_[p]) := lt_of_le_of_ne (integer_nonnegative p n) (Ne.symm hn)
  rw [Int.cast_sub,Int.cast_one,Padic.addValuation.map_sub_eq_of_lt_right
    (by simpa only [Padic.addValuation.map_one] using hp),Padic.addValuation.map_one]

/-- A comparison of the two actual quotient families bootstraps both to
integrality, because at least one of the neighboring integer denominators
is a p-adic unit. It does not assume either root label is a p-adic unit. -/
theorem neighboring_ratios (n u v:ℤ) (L M:ℚ_[p])
    (hL:Padic.addValuation L=Padic.addValuation ((u:ℚ_[p])/(n:ℚ_[p])))
    (hM:Padic.addValuation M=Padic.addValuation ((v:ℚ_[p])/((n-1:ℤ):ℚ_[p])))
    (hcross:0≤Padic.addValuation (L-M)) :
    0≤Padic.addValuation L ∧ 0≤Padic.addValuation M ∧
      0≤Padic.addValuation ((u:ℚ_[p])/(n:ℚ_[p])) ∧
      0≤Padic.addValuation ((v:ℚ_[p])/((n-1:ℤ):ℚ_[p])) := by
  have hint:0≤Padic.addValuation L ∧ 0≤Padic.addValuation M := by
    rcases neighboring_unit p n with hn|hn
    · have hl:0≤Padic.addValuation L := by
        rw [hL,Padic.addValuation.map_div,hn,sub_zero]
        exact integer_nonnegative p u
      have hm:=Padic.addValuation.map_le_sub hl hcross
      exact ⟨hl,by simpa only [sub_sub_cancel] using hm⟩
    · have hm:0≤Padic.addValuation M := by
        rw [hM,Padic.addValuation.map_div,hn,sub_zero]
        exact integer_nonnegative p v
      have hl:=Padic.addValuation.map_le_add hcross hm
      exact ⟨by simpa only [sub_add_cancel] using hl,hm⟩
  exact ⟨hint.1,hint.2,by rw [←hL]; exact hint.1,by rw [←hM]; exact hint.2⟩

end RatioIntegrality318
#print axioms RatioIntegrality318.neighboring_ratios
