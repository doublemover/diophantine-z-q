module
public import ActualSingularResidueCount318
public section
noncomputable section
namespace ActualFullLocalDensityRecurrence318
open QuadricCRTAssembly318 ActualPrimitivePrimePower318 ActualSingularResidueCount318
set_option maxHeartbeats 24000000

@[expose] def count (κ : ℤ) (p e : ℕ) : ℕ := Nat.card (Quadric (κ:ZMod (p^e)))
@[expose] def volume (κ : ℤ) (p e : ℕ) : ℚ := (count κ p e:ℚ)/(p:ℚ)^(4*e)

lemma actual_level_zero (κ : ℤ) (p : ℕ) : count κ p 0=1 := by
  unfold count
  rw [pow_zero]
  letI : Unique (Quadric (κ:ZMod 1)) := {
    default := PrimitiveSieveCRT318.origin (κ:ZMod 1)
    uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
  simp only [Nat.card_eq_fintype_card,Fintype.card_unique]

lemma actual_level_one (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) : count κ p 1=p^4 := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold count
  rw [pow_one,Nat.card_congr (PrimitiveSieveCRT318.fieldEquiv (κ:ZMod p))]
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  simpa only [ZMod.card] using FiniteFiveQuadricCount318.quadric_card hF
    (GoodReductionResidue318.two_residue_ne p hp2) (κ:ZMod p) hk

/-- Genuine original singular/primitive decomposition produces the
full local recurrence, including the base step from modulus1 to p^2. -/
theorem actual_whole_prime_power_recurrence (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    count κ p (e+2)=(p^4-1)*(p^4)^(e+1)+p^5*count κ p e := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hh := actual_whole_quadric_split κ (p^e) p
  have he : p*(p^e*p)=p^(e+2) := by
    rw [show e+2=(e+1)+1 by omega,pow_succ,pow_succ]
    ring
  rw [he,actual_primitive_prime_power_count κ p hp hp2 hκ (e+1)] at hh
  simpa only [count,mul_comm] using hh

/-- Normalized recurrence on the actual original WHOLE residue count.
This is not yet a claim that its sequence converges. -/
theorem actual_whole_volume_recurrence (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    volume κ p (e+2)=1-1/(p:ℚ)^4+volume κ p e/(p:ℚ)^3 := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hp4 : 1≤p^4 := one_le_pow₀ (show 1≤p by omega)
  unfold volume
  rw [actual_whole_prime_power_recurrence κ p hp hp2 hκ e]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp4,Nat.cast_one,Nat.cast_pow]
  have hden : (p:ℚ)^(4*(e+2))=(p:ℚ)^(4*e)*(p:ℚ)^8 := by
    rw [show 4*(e+2)=4*e+8 by omega,pow_add]
  have hnum : ((p:ℚ)^4)^(e+1)=(p:ℚ)^(4*e)*(p:ℚ)^4 := by
    rw [pow_succ ((p:ℚ)^4) e,←pow_mul]
  rw [hden,hnum]
  field_simp [hp0]
  <;> ring

end ActualFullLocalDensityRecurrence318
