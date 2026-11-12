module
public import ActualOriginalRationalArcSeparation318
public section
noncomputable section
namespace ActualOriginalMajorArcDomain318
open ActualOriginalRationalArcSeparation318 MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

abbrev ArcIndex (N : ℕ) := (q : Fin N) × {a : ZMod (q.val+1) // IsUnit a}
@[expose] def code {N : ℕ} (i : ArcIndex N) : ℕ × ℕ := (i.1.val,i.2.val.val)
@[expose] def center {N : ℕ} (i : ArcIndex N) : ℝ :=
  (i.2.val.val : ℝ)/(i.1.val+1 : ℕ)
@[expose] def radius (N : ℕ) (B : ℝ) : ℝ := (N : ℝ)/B^2
@[expose] def arc {N : ℕ} (B : ℝ) (i : ArcIndex N) : Set ℝ :=
  Set.Ioc (center i-radius N B) (center i+radius N B)
@[expose] def majorDomain (N : ℕ) (B : ℝ) : Set ℝ := ⋃ i : ArcIndex N, arc B i
@[expose] def fundamental (N : ℕ) (B : ℝ) : Set ℝ :=
  Set.Ioc (-radius N B) (1-radius N B)
@[expose] def minorDomain (N : ℕ) (B : ℝ) : Set ℝ := fundamental N B \ majorDomain N B

lemma code_injective (N : ℕ) : Function.Injective (code (N:=N)) := by
  rintro ⟨q,a⟩ ⟨r,b⟩ h
  have hq : q=r := Fin.ext (congrArg Prod.fst h)
  cases hq
  have ha : a=b := Subtype.ext (ZMod.val_injective (congrArg Prod.snd h))
  cases ha
  rfl

lemma center_bounds {N : ℕ} (i : ArcIndex N) :
    0 ≤ center i ∧ center i+1/(N : ℝ) ≤ 1 := by
  have hq : (0 : ℝ) < (i.1.val+1 : ℕ) := by positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) i.1.isLt)
  have hqN : ((i.1.val+1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show i.1.val+1≤N by omega)
  have ha : (i.2.val.val : ℝ)+1 ≤ (i.1.val+1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ZMod.val_lt i.2.val))
  have hd : (i.2.val.val : ℝ)/((i.1.val+1 : ℕ) : ℝ)+1/((i.1.val+1 : ℕ) : ℝ) ≤ 1 := by
    rw [←add_div]
    exact (div_le_one hq).mpr ha
  have hrec := one_div_le_one_div_of_le hq hqN
  exact ⟨by unfold center; positivity,by change _ ≤ 1; dsimp [center]; linarith⟩

lemma radius_small (N : ℕ) (hN : 0 < N) (B : ℝ) (hB : 0 < B)
    (hscale : ((N : ℝ)+1)^3 ≤ B) : 2*radius N B < 1/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 2*(N : ℝ)+1 ≤ B := by
    nlinarith [sq_nonneg (N : ℝ),mul_nonneg hn.le (sq_nonneg (N : ℝ))]
  have hsq : 2*(N : ℝ)^2 < B^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hb)
      (show 0 ≤ B+(2*(N : ℝ)+1) by positivity)
    nlinarith [sq_nonneg (N : ℝ)]
  unfold radius
  rw [←mul_div_assoc]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hB) hn).mpr
  nlinarith

lemma arc_subset_fundamental {N : ℕ} (hN : 0 < N) (B : ℝ) (hB : 0 < B)
    (hscale : ((N : ℝ)+1)^3 ≤ B) (i : ArcIndex N) : arc B i ⊆ fundamental N B := by
  have hc := center_bounds i
  have hr := radius_small N hN B hB hscale
  intro x hx
  change center i-radius N B < x ∧ x ≤ center i+radius N B at hx
  change -radius N B < x ∧ x ≤ 1-radius N B
  constructor <;> linarith [hc.1,hc.2,hx.1,hx.2]

lemma major_subset_fundamental (N : ℕ) (hN : 0 < N) (B : ℝ) (hB : 0 < B)
    (hscale : ((N : ℝ)+1)^3 ≤ B) : majorDomain N B ⊆ fundamental N B := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  exact arc_subset_fundamental hN B hB hscale i hi

lemma arcs_pairwise (N : ℕ) (B : ℝ) (hB : 0 < B)
    (hscale : ((N : ℝ)+1)^3 ≤ B) : Pairwise (Disjoint on (arc (N:=N) B)) := by
  intro i j hij
  have hc : code i ≠ code j := fun h => hij (code_injective N h)
  have hd := actual_unit_arc_separation N i.1 j.1 i.2 j.2 hc B hB hscale 0 0
  simp only [Int.cast_zero,add_zero] at hd
  exact hd.mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self

lemma major_measurable (N : ℕ) (B : ℝ) : MeasurableSet (majorDomain N B) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioc)
lemma minor_measurable (N : ℕ) (B : ℝ) : MeasurableSet (minorDomain N B) :=
  measurableSet_Ioc.diff (major_measurable N B)

end ActualOriginalMajorArcDomain318
