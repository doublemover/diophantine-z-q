module
public import ActualOriginalArcDiagonal318
public import Mathlib.Data.Nat.GCD.Basic
public section
noncomputable section
namespace ActualOriginalRationalArcSeparation318
open ActualOriginalArcDiagonal318
set_option maxHeartbeats 16000000

/-- Distinct canonical reduced fractions are distinct even modulo an
integer. The modulus-one numerator zero is included. -/
lemma reduced_cross_ne_zero (a b q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (ha : a < q) (hb : b < r) (hqa : Nat.Coprime a q) (hrb : Nat.Coprime b r)
    (hne : a ≠ b ∨ q ≠ r) (k : ℤ) :
    (a : ℤ)*r-(b : ℤ)*q-k*q*r ≠ 0 := by
  intro hz
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hzR : (a : ℝ)*r-(b : ℝ)*q-(k : ℝ)*q*r = 0 := by exact_mod_cast hz
  have hf : (a : ℝ)/q-(b : ℝ)/r = (k : ℝ) := by
    field_simp [hqR.ne',hrR.ne']
    nlinarith [hzR]
  have ha0 : (0 : ℝ) ≤ (a : ℝ)/q := by positivity
  have hb0 : (0 : ℝ) ≤ (b : ℝ)/r := by positivity
  have ha1 : (a : ℝ)/q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast ha)
  have hb1 : (b : ℝ)/r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast hb)
  have hkL : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < (k : ℝ) by linarith)
  have hkU : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  have hk : k = 0 := by omega
  subst k
  have hc : a*r = b*q := by
    simp only [zero_mul,sub_zero] at hz
    have hz' : (a : ℤ)*r = (b : ℤ)*q := sub_eq_zero.mp hz
    exact_mod_cast hz'
  have hqr : q ∣ r := hqa.symm.dvd_of_dvd_mul_left
    (show q ∣ a*r from ⟨b,by simpa only [mul_comm] using hc⟩)
  have hrq : r ∣ q := hrb.symm.dvd_of_dvd_mul_left
    (show r ∣ b*q from ⟨a,by simpa only [mul_comm] using hc.symm⟩)
  have hqrEq : q = r := Nat.dvd_antisymm hqr hrq
  have hab : a = b := by rw [←hqrEq] at hc; nlinarith
  exact hne.elim (fun h => h hab) (fun h => h hqrEq)

lemma integer_abs_cast_ge_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hi : z ≤ -1 := by omega
    have hr : (z : ℝ) ≤ -1 := by exact_mod_cast hi
    rw [abs_of_neg (by linarith)]
    linarith
  · have hi : 1 ≤ z := by omega
    have hr : (1 : ℝ) ≤ z := by exact_mod_cast hi
    rw [abs_of_pos (by linarith)]
    exact hr

/-- A genuine quantitative circle separation, valid for EVERY integer
representative shift, with denominator product at most N². -/
theorem reduced_fraction_separation (N a b q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hqN : q ≤ N) (hrN : r ≤ N) (ha : a < q) (hb : b < r)
    (hqa : Nat.Coprime a q) (hrb : Nat.Coprime b r) (hne : a ≠ b ∨ q ≠ r) (k : ℤ) :
    1/(N : ℝ)^2 ≤ |(a : ℝ)/q-(b : ℝ)/r-(k : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hq hqN)
  have hcross := integer_abs_cast_ge_one _ (reduced_cross_ne_zero a b q r hq hr ha hb hqa hrb hne k)
  have heq : (a : ℝ)/q-(b : ℝ)/r-(k : ℝ) =
      (((a : ℤ)*r-(b : ℤ)*q-k*q*r : ℤ) : ℝ) / ((q : ℝ)*r) := by
    push_cast
    field_simp [hqR.ne',hrR.ne']
    <;> ring
  rw [heq,abs_div,abs_of_pos (mul_pos hqR hrR)]
  have hprod : (q : ℝ)*r ≤ (N : ℝ)^2 := by
    have hq' : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have hr' : (r : ℝ) ≤ N := by exact_mod_cast hrN
    calc
      (q : ℝ)*r ≤ (N : ℝ)*r := mul_le_mul_of_nonneg_right hq' hrR.le
      _ ≤ (N : ℝ)*N := mul_le_mul_of_nonneg_left hr' hN.le
      _ = _ := by ring
  calc
    _ ≤ 1/((q : ℝ)*r) := one_div_le_one_div_of_le (mul_pos hqR hrR) hprod
    _ ≤ _ := div_le_div_of_nonneg_right hcross (mul_pos hqR hrR).le

/-- At the actual diagonal scales, two such lifted closed arcs cannot
meet. This handles wrap-around by retaining independent integer lifts. -/
theorem disjoint_lifted_arcs (N a b q r : ℕ) (hN : 0 < N)
    (hq : 0 < q) (hr : 0 < r) (hqN : q ≤ N) (hrN : r ≤ N)
    (ha : a < q) (hb : b < r) (hqa : Nat.Coprime a q) (hrb : Nat.Coprime b r)
    (hne : a ≠ b ∨ q ≠ r) (B : ℝ) (hB : 0 < B) (hscale : ((N : ℝ)+1)^3 ≤ B)
    (k l : ℤ) :
    Disjoint (Set.Icc ((a : ℝ)/q+(k : ℝ)-(N : ℝ)/B^2) ((a : ℝ)/q+(k : ℝ)+(N : ℝ)/B^2))
      (Set.Icc ((b : ℝ)/r+(l : ℝ)-(N : ℝ)/B^2) ((b : ℝ)/r+(l : ℝ)+(N : ℝ)/B^2)) := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : ℝ)^3+1 ≤ ((N : ℝ)+1)^3 := by nlinarith [sq_nonneg (N : ℝ)]
  have hsq : 2*(N : ℝ)^3 < B^2 := by
    have hp : 0 ≤ (N : ℝ)^3 := by positivity
    have hBB : ((N : ℝ)^3+1)^2 ≤ B^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hc.trans hscale))
        (show 0 ≤ B+((N : ℝ)^3+1) by positivity)]
    nlinarith [sq_nonneg ((N : ℝ)^3)]
  have hrad : 2*((N : ℝ)/B^2) < 1/(N : ℝ)^2 := by
    rw [←mul_div_assoc]
    apply (div_lt_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hnR)).mpr
    nlinarith [hsq]
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hs := reduced_fraction_separation N a b q r hq hr hqN hrN ha hb hqa hrb hne (l-k)
  rw [Int.cast_sub] at hs
  have hu : |(a : ℝ)/q-(b : ℝ)/r-((l : ℝ)-(k : ℝ))| ≤ 2*((N : ℝ)/B^2) := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  linarith

/-- Literal unit-numerator indices used by majorArcIntegral satisfy the
reduced-fraction hypotheses, so distinct original indices give disjoint
lifted arcs, including the wrapped modulus-one arc. -/
theorem actual_unit_arc_separation (N : ℕ) (q r : Fin N)
    (a : {a : ZMod (q.val+1) // IsUnit a})
    (b : {b : ZMod (r.val+1) // IsUnit b})
    (hne : (q.val,a.val.val) ≠ (r.val,b.val.val))
    (B : ℝ) (hB : 0 < B) (hscale : ((N : ℝ)+1)^3 ≤ B) (k l : ℤ) :
    Disjoint
      (Set.Icc ((a.val.val : ℝ)/(q.val+1 : ℕ)+(k : ℝ)-(N : ℝ)/B^2)
        ((a.val.val : ℝ)/(q.val+1 : ℕ)+(k : ℝ)+(N : ℝ)/B^2))
      (Set.Icc ((b.val.val : ℝ)/(r.val+1 : ℕ)+(l : ℝ)-(N : ℝ)/B^2)
        ((b.val.val : ℝ)/(r.val+1 : ℕ)+(l : ℝ)+(N : ℝ)/B^2)) := by
  have hqa : Nat.Coprime a.val.val (q.val+1) :=
    (ZMod.isUnit_iff_coprime a.val.val (q.val+1)).mp (by simpa using a.property)
  have hrb : Nat.Coprime b.val.val (r.val+1) :=
    (ZMod.isUnit_iff_coprime b.val.val (r.val+1)).mp (by simpa using b.property)
  have hd : a.val.val ≠ b.val.val ∨ q.val+1 ≠ r.val+1 := by
    by_contra h
    push_neg at h
    exact hne (Prod.ext (by omega) h.1)
  exact disjoint_lifted_arcs N a.val.val b.val.val (q.val+1) (r.val+1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (ZMod.val_lt _) (ZMod.val_lt _) hqa hrb hd B hB hscale k l

end ActualOriginalRationalArcSeparation318
