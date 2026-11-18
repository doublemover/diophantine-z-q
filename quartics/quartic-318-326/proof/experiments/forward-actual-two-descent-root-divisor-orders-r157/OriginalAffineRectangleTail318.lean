module
public import OriginalShearBoxBudget318
public section
noncomputable section
namespace OriginalAffineRectangleTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 IntegerResidueBoxCount318
open OriginalAffinePointTail318 OriginalAffineSieveEliminants318 OriginalOffsetEliminant318
open OriginalOffsetZeroLocus318 OriginalUniformEliminantHeight318
open OriginalShearBoxBudget318 OriginalBoundedIntegerShear318
open OriginalControlledIntegralBasis318 OriginalEuclideanLattice318
set_option maxHeartbeats 8000000

/-- Actual coefficient triples, with one original prime obstruction
witness on the SAME affine fiber. A sigma retains the original offsets. -/
@[expose] def RectangleBad (side : Bool) (κ t : ℤ) (u v d : Vector ℤ) (A B C Y : ℕ) :=
  Σ a : Interval A×Interval B, FiberBad side κ t (offset u v a.1.1 a.2.1) d C Y

lemma fiber_trivial (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (C Y : ℕ) :
    Nat.card (FiberBad side κ t a d C Y)≤2*C+1 := by
  have hh := Nat.card_le_card_of_injective
    (Subtype.val : FiberBad side κ t a d C Y → Interval C) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card,Interval,Fintype.card_coe,interval_card] using hh

/-- Generic finite fiber summation, exposing the exceptional fibers as a
counted subset instead of silently applying a nonzero-value lemma there. -/
lemma sum_with_bad_fibers {X : Type*} [Fintype X] (n : X → ℕ) (bad : X → Prop)
    (l H K : ℝ) (hl : 0≤l) (hH : 0≤H) (hK : 0≤K)
    (good : ∀ x, ¬bad x → (n x:ℝ)*l≤H)
    (exceptional : ∀ x, bad x → (n x:ℝ)*l≤K) :
    (∑ x, (n x:ℝ))*l≤(Fintype.card X:ℝ)*H+(Nat.card {x : X // bad x}:ℝ)*K := by
  classical
  have hp (x : X) : (n x:ℝ)*l≤H+(if bad x then K else 0) := by
    by_cases hx : bad x
    · simpa [hx] using (exceptional x hx).trans (le_add_of_nonneg_left hH)
    · simpa [hx] using good x hx
  have hc : (Nat.card {x : X // bad x}:ℝ)=∑ x, (if bad x then (1:ℝ) else 0) := by
    have hh : Nat.card {x : X // bad x}=∑ x, (if bad x then (1:ℕ) else 0) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter]
    exact_mod_cast hh
  have hs : (∑ x, if bad x then K else 0)=(Nat.card {x : X // bad x}:ℝ)*K := by
    rw [hc,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hh : bad x <;> simp [hh]
  calc
    _ = ∑ x, (n x:ℝ)*l := Finset.sum_mul.symm
    _ ≤ ∑ x, H+(if bad x then K else 0) := Finset.sum_le_sum (fun x _ => hp x)
    _ = _ := by rw [Finset.sum_add_distrib,hs];simp

/-- All actual offsets are summed, using one uniform constructed height
and retaining the two actual zero-value offset loci. -/
theorem regular_rectangle (side : Bool) (κ t : ℤ) (u v d : Vector ℤ)
    (A B C Y : ℕ) (hY : 1<Y) (N : ℝ) (hN : 1≤N)
    (hheight : ∀ a : Interval A×Interval B, ∀ coordinate,
      |(normEliminant side κ t (offset u v a.1.1 a.2.1) d coordinate:ℝ)|≤N)
    (hn : ∀ coordinate, polynomial side coordinate κ t u v d≠0) :
    (Nat.card (RectangleBad side κ t u v d A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*4*Real.log N+
        8*((2*A+1:ℕ)+(2*B+1):ℝ)*(2*C+1)*Real.log (Y:ℝ) := by
  classical
  let bad : Interval A×Interval B → Prop := fun a => ∃ coordinate : Bool,
    normEliminant side κ t (offset u v a.1.1 a.2.1) d coordinate=0
  let n : Interval A×Interval B → ℕ := fun a =>
    Nat.card (FiberBad side κ t (offset u v a.1.1 a.2.1) d C Y)
  have hl : 0≤Real.log (Y:ℝ) := (Real.log_pos (by exact_mod_cast hY)).le
  have hlN : 0≤Real.log N := Real.log_nonneg hN
  have hh := sum_with_bad_fibers n bad (Real.log (Y:ℝ)) (4*Real.log N)
    ((2*C+1)*Real.log (Y:ℝ)) hl (by positivity) (by positivity) (by
      intro a ha
      have hx : normEliminant side κ t (offset u v a.1.1 a.2.1) d false≠0 := fun he => ha ⟨false,he⟩
      have hz : normEliminant side κ t (offset u v a.1.1 a.2.1) d true≠0 := fun he => ha ⟨true,he⟩
      have hb := regular_fiber_tail side κ t _ d C Y hY hx hz N N (hheight a false) (hheight a true)
      dsimp [n]
      nlinarith only [hb]) (by
      intro a ha
      have hb : (n a:ℝ)≤2*C+1 := by exact_mod_cast fiber_trivial side κ t _ d C Y
      exact mul_le_mul_of_nonneg_right hb hl)
  have hzero : (Nat.card {a : Interval A×Interval B // bad a}:ℝ)≤
      8*((2*A+1:ℕ)+(2*B+1):ℝ) := by
    exact_mod_cast either_zero_offsets side κ t u v d A B hn
  have hcard : (Nat.card (RectangleBad side κ t u v d A B C Y):ℝ)=∑ a, (n a:ℝ) := by
    simp only [RectangleBad,Nat.card_eq_fintype_card,Fintype.card_sigma,n,Nat.cast_sum]
  have hall : Fintype.card (Interval A×Interval B)=(2*A+1)*(2*B+1) := by
    simp only [Fintype.card_prod,Interval,Fintype.card_coe,interval_card]
  rw [hcard]
  rw [hall] at hh
  have hmul := mul_le_mul_of_nonneg_right hzero (show 0≤(2*C+1:ℝ)*Real.log (Y:ℝ) by positivity)
  push_cast at hh hmul ⊢
  nlinarith only [hh,hmul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual same-basis regular rectangle endpoint. The nonzero
polynomials and ALL uniform heights are produced internally. -/
theorem original_regular_rectangle (q : ι → ℕ) (hq : ∀ k, (q k).Prime) (κ t : ℤ)
    (hκ : κ≠0) (s : ∀ k, Option (ZMod (q k))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (i j : ℕ) (hi : i<5) (hj : j<5)
    (hw : (shear (i:ℤ) (j:ℤ) u v z).2.2≠0)
    (side : Bool) (ht : side=true → t+2≠0) (A B C Y : ℕ) (hY : 1<Y) :
    let N := 1+regularHeight κ t (heightRadius A B ‖embed w‖)
    (Nat.card (RectangleBad side κ t u v (shear (i:ℤ) (j:ℤ) u v z) A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*4*Real.log N+
        8*((2*A+1:ℕ)+(2*B+1):ℝ)*(2*C+1)*Real.log (Y:ℝ) := by
  dsimp only
  apply regular_rectangle side κ t u v _ A B C Y hY
  · dsimp [regularHeight]
    positivity
  · intro a coordinate
    obtain ⟨ha,hd⟩ := uniform_box u v w z huv hvw hz A B i j hi hj a.1 a.2
    have hh := actual_regular_height side coordinate κ t _ _ _
      (by dsimp [heightRadius];positivity) ha hd
    linarith
  · intro coordinate
    exact OriginalShearedOffsetNonzero318.actual_offset_nonzero q hq κ t hκ s u v z hb
      (i:ℤ) (j:ℤ) hw side coordinate ht

/-- The exceptional original second pair has no bad offset locus: its
unpadded eliminants are positive on EVERY offset of a transverse shear. -/
theorem exceptional_rectangle (κ t : ℤ) (ht : t+2=0) (u v d : Vector ℤ)
    (hdx : d.1≠0) (hdz : d.2.1≠0) (A B C Y : ℕ) (hY : 2≤Y)
    (N : ℝ) (hheight : ∀ a : Interval A×Interval B,
      |(OriginalLinearNormEliminant318.eliminant t
        (offset u v a.1.1 a.2.1).1 (offset u v a.1.1 a.2.1).2.1 d.1 d.2.1:ℝ)|≤N ∧
      |(OriginalLinearNormEliminant318.eliminant t
        (offset u v a.1.1 a.2.1).2.1 (offset u v a.1.1 a.2.1).1 d.2.1 d.1:ℝ)|≤N) :
    (Nat.card (RectangleBad true κ t u v d A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*4*Real.log N := by
  classical
  have hb (a : Interval A×Interval B) :
      (Nat.card (FiberBad true κ t (offset u v a.1.1 a.2.1) d C Y):ℝ)*Real.log (Y:ℝ)≤4*Real.log N := by
    have hh := exceptional_fiber_tail κ t ht _ d hdx hdz C Y hY N N (hheight a).1 (hheight a).2
    nlinarith only [hh]
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => hb a)
  rw [←Finset.sum_mul] at hh
  have hc : (Nat.card (RectangleBad true κ t u v d A B C Y):ℝ)=
      ∑ a : Interval A×Interval B, (Nat.card (FiberBad true κ t (offset u v a.1.1 a.2.1) d C Y):ℝ) := by
    simp only [RectangleBad,Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  rw [hc]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Interval,Fintype.card_coe,
    interval_card,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_assoc] using hh

@[expose] def bothHeight (κ t : ℤ) (L : ℝ) :=
  1+regularHeight κ t L+exceptionalHeight t L

/-- One uniform bound for BOTH original pairs, including t=-2. Original
whole-basis, actual frame boxes, polynomial nonvanishing and exceptional
positive eliminants are consumed here, not left as height/locus premises. -/
theorem original_rectangle (q : ι → ℕ) (hq : ∀ k, (q k).Prime) (κ t : ℤ)
    (hκ : κ≠0) (s : ∀ k, Option (ZMod (q k))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hz : ‖embed z‖≤2*‖embed w‖) (i j : ℕ) (hi : i<5) (hj : j<5)
    (hw : (shear (i:ℤ) (j:ℤ) u v z).2.2≠0)
    (htrans : t+2=0 → (shear (i:ℤ) (j:ℤ) u v z).1≠0 ∧
      (shear (i:ℤ) (j:ℤ) u v z).2.1≠0)
    (side : Bool) (A B C Y : ℕ) (hY : 2≤Y) :
    let N := bothHeight κ t (heightRadius A B ‖embed w‖)
    (Nat.card (RectangleBad side κ t u v (shear (i:ℤ) (j:ℤ) u v z) A B C Y):ℝ)*Real.log (Y:ℝ)≤
      ((2*A+1:ℕ):ℝ)*(2*B+1)*4*Real.log N+
        8*((2*A+1:ℕ)+(2*B+1):ℝ)*(2*C+1)*Real.log (Y:ℝ) := by
  let L := heightRadius A B ‖embed w‖
  let N := bothHeight κ t L
  have hL : 0≤L := by dsimp [L,heightRadius];positivity
  have hr : 0≤regularHeight κ t L := by dsimp [regularHeight];positivity
  have he : 0≤exceptionalHeight t L := by dsimp [exceptionalHeight];positivity
  have hN : 1≤N := by dsimp [N,bothHeight];linarith
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  by_cases hex : side=true ∧ t+2=0
  · rcases hex with ⟨rfl,ht⟩
    obtain ⟨hdx,hdz⟩ := htrans ht
    have hh := exceptional_rectangle κ t ht u v (shear (i:ℤ) (j:ℤ) u v z) hdx hdz A B C Y hY N (by
      intro a
      obtain ⟨ha,hd⟩ := uniform_box u v w z huv hvw hz A B i j hi hj a.1 a.2
      have hx := actual_exceptional_height t _ _ _ _ L hL ha.1 ha.2.1 hd.1 hd.2.1
      have hz' := actual_exceptional_height t _ _ _ _ L hL ha.2.1 ha.1 hd.2.1 hd.1
      refine ⟨hx.trans ?_,hz'.trans ?_⟩ <;> dsimp [N,bothHeight] <;> linarith)
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · apply regular_rectangle side κ t u v _ A B C Y (by omega) N hN
    · intro a coordinate
      obtain ⟨ha,hd⟩ := uniform_box u v w z huv hvw hz A B i j hi hj a.1 a.2
      have hh := actual_regular_height side coordinate κ t _ _ L hL ha hd
      exact hh.trans (by dsimp [N,bothHeight];linarith)
    · intro coordinate
      apply OriginalShearedOffsetNonzero318.actual_offset_nonzero q hq κ t hκ s u v z hb
        (i:ℤ) (j:ℤ) hw side coordinate
      intro hs ht
      exact hex ⟨hs,ht⟩

end OriginalAffineRectangleTail318
