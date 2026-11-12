module
public import ActualOddBadBaseCount318
public section
noncomputable section
namespace ActualOddBadLocalRecurrence318
open QuadricCRTAssembly318 FiniteNormDifferenceCount318 ActualOddBadBaseCount318
open ActualFullLocalDensityRecurrence318 ActualSingularResidueCount318
set_option maxHeartbeats 26000000

@[expose] def zeroQuadricEquiv {F : Type*} [Field F] (κ : F) (hκ : κ=0) :
    Quadric κ ≃ NormDifference (0:F)×F where
  toFun x := (⟨(x.1.1,x.1.2.1),by simpa only [equation,hκ,zero_mul,sub_zero] using x.2⟩,x.1.2.2)
  invFun z := ⟨(z.1.1.1,z.1.1.2,z.2),by simpa only [equation,hκ,zero_mul,sub_zero] using z.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma actual_bad_level_one (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) :
    (count κ p 1:ℤ)=(p:ℤ)^4+p^3-p^2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk : (κ:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mpr hκ
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hcard : Nat.card (ZMod p)=p := by simp only [Nat.card_eq_fintype_card,ZMod.card]
  unfold count
  rw [pow_one,Nat.card_congr (zeroQuadricEquiv (κ:ZMod p) hk),Nat.card_prod,hcard,Nat.cast_mul,
    difference_count hF (GoodReductionResidue318.two_residue_ne p hp2) (0:ZMod p)]
  simp only [if_pos rfl,ZMod.card]
  ring

theorem actual_bad_whole_recurrence (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (e : ℕ) :
    (count κ p (e+2):ℤ)=((p:ℤ)^4+p^3-p^2-p)*((p:ℤ)^4)^(e+1)+p^5*(count κ p e:ℤ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hh := actual_whole_quadric_split κ (p^e) p
  have he : p*(p^e*p)=p^(e+2) := by
    rw [show e+2=(e+1)+1 by omega,pow_succ p (e+1),pow_succ p e]
    ring
  rw [he] at hh
  have hc := congrArg (fun n : ℕ => (n:ℤ)) hh
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    actual_valuation_one_primitive_count κ p hp hp2 hκ hκ2 e] at hc
  simpa only [count,mul_comm] using hc

@[expose] def primitiveFactor (p : ℕ) : ℚ := 1+1/(p:ℚ)-1/(p:ℚ)^2-1/(p:ℚ)^3
@[expose] def firstVolume (p : ℕ) : ℚ := 1+1/(p:ℚ)-1/(p:ℚ)^2
lemma actual_bad_volume_one (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) : volume κ p 1=firstVolume p := by
  have hcount : (count κ p 1:ℚ)=(p:ℚ)^4+p^3-p^2 := by
    exact_mod_cast actual_bad_level_one κ p hp hp2 hκ
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  unfold volume firstVolume
  rw [hcount]
  simp only [mul_one]
  field_simp [hp0]
  <;> ring

/-- The valuation-one prime has its own genuine primitive term.
The good-prime factor 1-p^-4 is NOT reused at this bad place. -/
theorem actual_bad_volume_recurrence (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : (p:ℤ)∣κ) (hκ2 : ¬(p:ℤ)^2∣κ) (e : ℕ) :
    volume κ p (e+2)=primitiveFactor p+volume κ p e/(p:ℚ)^3 := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hc : (count κ p (e+2):ℚ)=
      ((p:ℚ)^4+p^3-p^2-p)*((p:ℚ)^4)^(e+1)+p^5*(count κ p e:ℚ) := by
    exact_mod_cast actual_bad_whole_recurrence κ p hp hp2 hκ hκ2 e
  unfold volume primitiveFactor
  rw [hc]
  have hden : (p:ℚ)^(4*(e+2))=(p:ℚ)^(4*e)*(p:ℚ)^8 := by
    rw [show 4*(e+2)=4*e+8 by omega,pow_add]
  have hnum : ((p:ℚ)^4)^(e+1)=(p:ℚ)^(4*e)*(p:ℚ)^4 := by
    rw [pow_succ ((p:ℚ)^4) e,←pow_mul]
  rw [hden,hnum]
  field_simp [hp0]
  <;> ring

end ActualOddBadLocalRecurrence318
