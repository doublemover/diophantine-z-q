module
public import ActualTwoDescentChordPolynomial318
public section
noncomputable section
namespace ActualTwoDescentAdjustedChordSquares318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


variable [DecidableEq K]

def adjusted (D u : K) : K := if u=0 then D else u

lemma adjusted_nonzero (D u : K) (hD : D ≠ 0) : adjusted D u ≠ 0 := by
  by_cases hu : u=0
  · simpa only [adjusted,if_pos hu] using hD
  · simpa only [adjusted,if_neg hu] using hu

/-- A simple root of the cubic gives an actual nonzero square multiplier,
including a chord that meets the retained two-torsion point. -/
theorem actual_adjusted_chord_square (D u v w L m : K) (hD : D ≠ 0)
    (hp : u*v*w=L^2) (hd : D-2*m*L=u*v+u*w+v*w) :
    ∃ s : K, s ≠ 0 ∧ adjusted D u*adjusted D v*adjusted D w=s^2 := by
  have hz : ∀ a b c : K, a*b*c=0 → a*b*c=L^2 → L=0 := by
    intro a b c he hh
    rw [he] at hh
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hh.symm
  by_cases hu : u=0
  · have hL : L=0 := hz u v w (by rw [hu]; ring) hp
    have hvw : D=v*w := by rw [hu,hL] at hd; simpa using hd
    have hv : v ≠ 0 := by intro he; apply hD; rw [hvw,he]; ring
    have hw : w ≠ 0 := by intro he; apply hD; rw [hvw,he]; ring
    refine ⟨D,hD,?_⟩
    simp only [adjusted,if_pos hu,if_neg hv,if_neg hw]
    rw [hvw]
    ring
  by_cases hv : v=0
  · have hL : L=0 := hz u v w (by rw [hv]; ring) hp
    have huw : D=u*w := by rw [hv,hL] at hd; simpa using hd
    have hw : w ≠ 0 := by intro he; apply hD; rw [huw,he]; ring
    refine ⟨D,hD,?_⟩
    simp only [adjusted,if_neg hu,if_pos hv,if_neg hw]
    rw [huw]
    ring
  by_cases hw : w=0
  · have hL : L=0 := hz u v w (by rw [hw]; ring) hp
    have huv : D=u*v := by rw [hw,hL] at hd; simpa using hd
    refine ⟨D,hD,?_⟩
    simp only [adjusted,if_neg hu,if_neg hv,if_pos hw]
    rw [huv]
    ring
  · refine ⟨L,?_,?_⟩
    · intro he
      rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hp
      exact (mul_ne_zero (mul_ne_zero hu hv) hw) hp
    · simpa only [adjusted,if_neg hu,if_neg hv,if_neg hw] using hp

end ActualTwoDescentAdjustedChordSquares318
