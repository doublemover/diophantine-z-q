module
public import SelectedContactDenominators318
public section
noncomputable section
namespace ContactSmallPrimeRays318
open ScalarLocalSquares318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

lemma square_seventeen_one (k : ℤ) : IsSquare ((1+17*k:ℤ):ℤ_[17]) := by
  apply square_of_near_square 17 1
  have he : (1:ℤ_[17])^2-((1+17*k:ℤ):ℤ_[17])= -(17:ℤ_[17])*(k:ℤ_[17]) := by
    push_cast
    ring
  have hd : ‖(2:ℤ_[17])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hb : ‖(k:ℤ_[17])‖≤1 := PadicInt.norm_le_one _
  rw [he,norm_mul,norm_neg,mul_one,PadicInt.norm_p,hd]
  norm_num
  nlinarith

lemma unit_shape (p : ℕ) [Fact p.Prime] (k : ℤ) :
    padicValRat p ((1+(p:ℤ)*k:ℤ):ℚ)=0 := by
  rw [padicValRat.of_int]
  have he : padicValInt p (1+(p:ℤ)*k)=0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro h
    rw [Int.dvd_iff_emod_eq_zero] at h
    have hp : (1:ℤ)<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hm : (1:ℤ)%(p:ℤ)=1 := Int.emod_eq_of_lt (by norm_num) hp
    simp [Int.add_emod,Int.mul_emod,hm] at h
  simp [he]

/-- The actual required rational ray1mod(8*3*17) supplies both units and
Hensel-produced squares; local square roots are no longer extra inputs. -/
theorem ray_preparation (z : ℤ) (hz : (408:ℤ)∣z-1) :
    padicValRat 2 (z:ℚ)=0 ∧ IsSquare (z:ℚ_[2]) ∧
    padicValRat 3 (z:ℚ)=0 ∧ IsSquare (z:ℚ_[3]) ∧
    padicValRat 17 (z:ℚ)=0 ∧ IsSquare (z:ℚ_[17]) := by
  obtain ⟨k,hk⟩ := hz
  have h2 : z=1+8*(51*k) := by omega
  have h3 : z=1+3*(136*k) := by omega
  have h17 : z=1+17*(24*k) := by omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have he : z=1+2*(204*k) := by omega
    rw [he]
    exact unit_shape 2 _
  · rw [h2]
    simpa only [Rat.cast_intCast] using
      rational_square_of_integral 2 _ (square_two_shape (51*k))
  · rw [h3]
    exact unit_shape 3 _
  · rw [h3]
    simpa only [Rat.cast_intCast] using
      rational_square_of_integral 3 _ (square_three_shape (136*k))
  · rw [h17]
    exact unit_shape 17 _
  · rw [h17]
    simpa only [Rat.cast_intCast] using
      rational_square_of_integral 17 _ (square_seventeen_one (24*k))

end ContactSmallPrimeRays318
