module
public import OriginalTernaryBasis318
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Interval
public section
noncomputable section
namespace IntegerResidueBoxCount318
set_option maxHeartbeats 1000000

@[expose] def Interval (B : ℕ) := ↥(Finset.Icc (-(B:ℤ)) (B:ℤ))
@[expose] def ResidueBox (B m : ℕ) (a : ℤ) := {z : Interval B // (m:ℤ)∣z.1.1-a}

lemma shifted_bounds (B : ℕ) (z : Interval B) :
    0≤z.1+(B:ℤ) ∧ z.1+(B:ℤ)≤2*(B:ℤ) := by
  have hh := Finset.mem_Icc.mp z.2
  constructor <;> omega

lemma quotient_bounds (B m : ℕ) (hm : 0<m) (z : Interval B) :
    0≤(z.1+(B:ℤ))/(m:ℤ) ∧ (z.1+(B:ℤ))/(m:ℤ)≤((2*B/m:ℕ):ℤ) := by
  obtain ⟨hz0,hz1⟩ := shifted_bounds B z
  have hmz : (0:ℤ)<m := by exact_mod_cast hm
  refine ⟨Int.ediv_nonneg hz0 hmz.le,?_⟩
  have he : ((2*B/m:ℕ):ℤ)=(2*(B:ℤ))/(m:ℤ) := by simp only [Int.natCast_ediv,Int.natCast_mul]
  rw [he]
  exact Int.ediv_le_ediv hmz hz1

/-- Quotient after shifting the ORIGINAL interval, not a box in an assumed
basis. The residue itself is fixed, so this quotient is an injective code. -/
@[expose] def encode (B m : ℕ) (hm : 0<m) (a : ℤ) (z : ResidueBox B m a) :
    Fin (2*B/m+1) :=
  ⟨((z.1.1+(B:ℤ))/(m:ℤ)).toNat,by
    have hh := quotient_bounds B m hm z.1
    omega⟩

lemma encode_injective (B m : ℕ) (hm : 0<m) (a : ℤ) :
    Function.Injective (encode B m hm a) := by
  intro z w he
  have hz := quotient_bounds B m hm z.1
  have hw := quotient_bounds B m hm w.1
  have hi := congrArg Fin.val he
  change ((z.1.1+(B:ℤ))/(m:ℤ)).toNat=((w.1.1+(B:ℤ))/(m:ℤ)).toNat at hi
  have hq : (z.1.1+(B:ℤ))/(m:ℤ)=(w.1.1+(B:ℤ))/(m:ℤ) := by omega
  have hzm : Int.ModEq (m:ℤ) (a+(B:ℤ)) (z.1.1+(B:ℤ)) :=
    (Int.modEq_iff_dvd.mpr z.2).add_right (B:ℤ)
  have hwm : Int.ModEq (m:ℤ) (a+(B:ℤ)) (w.1.1+(B:ℤ)) :=
    (Int.modEq_iff_dvd.mpr w.2).add_right (B:ℤ)
  have hmod : (z.1.1+(B:ℤ))%(m:ℤ)=(w.1.1+(B:ℤ))%(m:ℤ) := hzm.symm.trans hwm
  have hzd := Int.mul_ediv_add_emod (z.1.1+(B:ℤ)) (m:ℤ)
  have hwd := Int.mul_ediv_add_emod (w.1.1+(B:ℤ)) (m:ℤ)
  rw [hq,hmod] at hzd
  apply Subtype.ext
  apply Subtype.ext
  exact add_right_cancel (hzd.symm.trans hwd)

/-- Uniform interval count for EVERY actual residue, including large or
negative representatives. -/
theorem residue_box_card (B m : ℕ) (hm : 0<m) (a : ℤ) :
    Nat.card (ResidueBox B m a)≤2*B/m+1 := by
  have hh := Nat.card_le_card_of_injective (encode B m hm a) (encode_injective B m hm a)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hh

end IntegerResidueBoxCount318
