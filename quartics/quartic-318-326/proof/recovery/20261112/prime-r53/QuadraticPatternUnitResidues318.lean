module
public import SelectedGaussianOrderPrimeSupport318
public section
noncomputable section
namespace QuadraticPatternUnitResidues318
open ClearedContactForms318
variable (q : ℕ) [Fact q.Prime]
lemma difference (u w k l : ℤ)
    (hk : (value u w k:ZMod q)=1) (hl : (value u w l:ZMod q)=1) :
    (k:ZMod q)=(l:ZMod q) ∨ (w:ZMod q)=0 := by
  have he : ((k:ZMod q)-(l:ZMod q))*(w:ZMod q)^2=0 := by
    simp only [value,Int.cast_add,Int.cast_mul,Int.cast_pow] at hk hl
    linear_combination hk-hl
  rcases mul_eq_zero.mp he with hkl|hw
  · exact Or.inl (sub_eq_zero.mp hkl)
  · have hm : (w:ZMod q)*(w:ZMod q)=0 := by simpa only [pow_two] using hw
    rcases mul_eq_zero.mp hm with hz|hz <;> exact Or.inr hz
/-- With two genuinely distinct coefficient residues, the SAME pair must
have w=0 and u=1 modulo q. This is necessary, not prime production. -/
lemma separated (u w k l : ℤ)
    (hk : (value u w k:ZMod q)=1) (hl : (value u w l:ZMod q)=1)
    (hkl : (k:ZMod q)≠(l:ZMod q)) : (w:ZMod q)=0 ∧ (u:ZMod q)=1 := by
  have hw := (difference q u w k l hk hl).resolve_left hkl
  exact ⟨hw,by simpa [value,hw] using hk⟩
lemma all_iff {ι : Type*} (k : ι→ℤ) (i j : ι) (u w : ℤ)
    (hij : (k i:ZMod q)≠(k j:ZMod q)) :
    (∀ t,(value u w (k t):ZMod q)=1) ↔ (w:ZMod q)=0 ∧ (u:ZMod q)=1 := by
  constructor
  · intro h
    exact separated q u w (k i) (k j) (h i) (h j) hij
  · rintro ⟨hw,hu⟩ t
    simp [value,hw,hu]
lemma divisor_support (u w k l : ℤ)
    (hk : (value u w k:ZMod q)=1) (hl : (value u w l:ZMod q)=1) :
    q∣(k-l).natAbs ∨ q∣w.natAbs := by
  rcases difference q u w k l hk hl with he|he
  · left
    have hz : ((k-l:ℤ):ZMod q)=0 := by simp [he]
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (k-l) q).mp hz
    simpa using Int.natAbs_dvd_natAbs.mpr hd
  · right
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd w q).mp he
    simpa using Int.natAbs_dvd_natAbs.mpr hd
end QuadraticPatternUnitResidues318
