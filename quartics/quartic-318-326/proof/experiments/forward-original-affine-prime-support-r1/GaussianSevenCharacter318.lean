module
public import FiniteQuadraticTwistCount318
public section
noncomputable section
namespace GaussianSevenCharacter318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma prime_mod_seven (a b : ℤ) (hnorm : (p:ℤ)=a^2+b^2)
    (ha : a%7=1) (hb : b%7=3) : p%7=3 := by
  have he : (p:ℤ)%7=3 := by
    rw [hnorm]
    norm_num [Int.add_emod,Int.pow_emod,ha,hb]
  exact_mod_cast he

/-- Ordinary reciprocity at the actual prime7 proves the required
nonsquare character, with both Jacobi arguments and their order explicit. -/
theorem seven_character (hp4 : p%4=1) (hp7 : p%7=3) :
    quadraticChar (ZMod p) (7:ZMod p)= -1 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hns : ¬IsSquare (3:ZMod 7) := by
    rintro ⟨x,hx⟩
    fin_cases x <;> norm_num at hx
  have hthree : jacobiSym (3:ℤ) 7= -1 := by
    rw [←legendreSym.to_jacobiSym]
    exact (legendreSym.eq_neg_one_iff (p:=7)).mpr hns
  have hcong : jacobiSym (p:ℤ) 7=jacobiSym (3:ℤ) 7 := by
    apply jacobiSym.mod_left'
    exact_mod_cast hp7
  have hrec := jacobiSym.quadratic_reciprocity_one_mod_four hp4 (by decide : Odd 7)
  change legendreSym p (7:ℤ)= -1
  rw [legendreSym.to_jacobiSym]
  exact hrec.symm.trans (hcong.trans hthree)

/-- Both historical Gaussian rays are used: mod16 for p1mod4 and mod7
for p3mod7. Neither conclusion is inferred from the rational408 ray. -/
theorem actual_seven_character (a b : ℤ) (hray : GaussianRayQuadratic318.Ray p a b)
    (ha7 : a%7=1) (hb7 : b%7=3) : quadraticChar (ZMod p) (7:ZMod p)= -1 := by
  have hm := GaussianRayQuadratic318.prime_mod p a b hray
  exact seven_character p (by omega) (prime_mod_seven p a b hray.1 ha7 hb7)

end GaussianSevenCharacter318
