module
public import OriginalDualIncidenceCount318
public import TriangularLatticeBoxCount318
public section
noncomputable section
namespace NonzeroMultipleBox318
open scoped BigOperators
open TernaryQuadraticLineCover318 IntegerResidueBoxCount318 TriangularLatticeBoxCount318
set_option maxHeartbeats 2000000

@[expose] def NonzeroBox (B : ℕ) := {v : Box B // coordinates v ≠ 0}
@[expose] def Divides (d : ℕ) (v : Vector ℤ) : Prop :=
  (d:ℤ)∣v.1 ∧ (d:ℤ)∣v.2.1 ∧ (d:ℤ)∣v.2.2
@[expose] def MultipleBox (B d : ℕ) := {v : NonzeroBox B // Divides d (coordinates v.1)}

lemma interval_zero_of_large_divisor (B d : ℕ) (hBd : B<d) (z : Interval B)
    (hz : (d:ℤ)∣z.1) : z.1=0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hz
  have hb := Finset.mem_Icc.mp z.2
  omega

/-- A nonzero vector divisible in all original coordinates cannot lie in a
box smaller than its divisor. This is where zero exclusion is essential. -/
theorem card_zero_of_large_divisor (B d : ℕ) (hBd : B<d) :
    Nat.card (MultipleBox B d)=0 := by
  classical
  haveI : IsEmpty (MultipleBox B d) := ⟨by
    intro v
    apply v.1.2
    obtain ⟨hx,hz,hw⟩ := v.2
    have ex := interval_zero_of_large_divisor B d hBd v.1.1.1 hx
    have ez := interval_zero_of_large_divisor B d hBd v.1.1.2.1 hz
    have ew := interval_zero_of_large_divisor B d hBd v.1.1.2.2 hw
    exact Prod.ext ex (Prod.ext ez ew)⟩
  exact Nat.card_of_isEmpty

/-- Inject into actual ORIGINAL residue intervals; no minimum or reduced
basis is assumed. Dropping nonzero here only enlarges the upper bound. -/
@[expose] def residueEmbedding (B d : ℕ) : MultipleBox B d →
    ResidueBox B d 0 × ResidueBox B d 0 × ResidueBox B d 0 := fun v =>
  (⟨v.1.1.1,by simpa only [sub_zero] using v.2.1⟩,
   ⟨v.1.1.2.1,by simpa only [sub_zero] using v.2.2.1⟩,
   ⟨v.1.1.2.2,by simpa only [sub_zero] using v.2.2.2⟩)

lemma residueEmbedding_injective (B d : ℕ) : Function.Injective (residueEmbedding B d) := by
  intro v w he
  apply Subtype.ext
  apply Subtype.ext
  have hx := congrArg (fun t => t.1.1) he
  have hz := congrArg (fun t => t.2.1.1) he
  have hw := congrArg (fun t => t.2.2.1) he
  exact Prod.ext hx (Prod.ext hz hw)

lemma residue_bound (B d : ℕ) (hd : 0<d) :
    Nat.card (MultipleBox B d)≤(2*B/d+1)^3 := by
  have hi := Nat.card_le_card_of_injective (residueEmbedding B d) (residueEmbedding_injective B d)
  have hr := residue_box_card B d hd 0
  have hh := Nat.mul_le_mul hr (Nat.mul_le_mul hr hr)
  calc
    _ ≤ Nat.card (ResidueBox B d 0)*
        (Nat.card (ResidueBox B d 0)*Nat.card (ResidueBox B d 0)) := by
      simpa only [Nat.card_prod] using hi
    _ ≤ (2*B/d+1)*((2*B/d+1)*(2*B/d+1)) := hh
    _ = (2*B/d+1)^3 := by ring

/-- Actual uniform weighted count, valid also when d>B or B=0. We keep a
slightly weaker d factor because it cancels the genuine zero-reduction
factor in the original dual-incidence count. -/
theorem weighted_count (B d : ℕ) (hd : 0<d) :
    d*Nat.card (MultipleBox B d)≤27*B^3 := by
  by_cases hdB : d≤B
  · have hs := interval_scaled B d hdB
    have hh := Nat.mul_le_mul hs (Nat.mul_le_mul hs hs)
    have hscaled : Nat.card (MultipleBox B d)*d^3≤27*B^3 := by
      calc
        _ ≤ (2*B/d+1)^3*d^3 := Nat.mul_le_mul_right _ (residue_bound B d hd)
        _ = ((2*B/d+1)*d)*(((2*B/d+1)*d)*((2*B/d+1)*d)) := by ring
        _ ≤ (3*B)*((3*B)*(3*B)) := hh
        _ = 27*B^3 := by ring
    have hd1 : 1≤d := hd
    have hd3 : d≤d^3 := by
      calc
        d = d*1*1 := by ring
        _ ≤ d*d*d := Nat.mul_le_mul (Nat.mul_le_mul_left d hd1) hd1
        _ = d^3 := by ring
    calc
      _ = Nat.card (MultipleBox B d)*d := Nat.mul_comm _ _
      _ ≤ Nat.card (MultipleBox B d)*d^3 := Nat.mul_le_mul_left _ hd3
      _ ≤ 27*B^3 := hscaled
  · rw [card_zero_of_large_divisor B d (Nat.lt_of_not_ge hdB),mul_zero]
    exact Nat.zero_le _

end NonzeroMultipleBox318
