module

public import SparseQuartic

public section

namespace CircuitReplay

abbrev Assignment := ℕ → ℚ
abbrev Row := Assignment → ℚ

@[expose] def Constraints (rows : List Row) (w : Assignment) : Prop :=
  ∀ r ∈ rows, r w = 0

@[expose] def HasSolution (rows : List Row) (q : ℚ) : Prop :=
  ∃ w, w 0 = q ∧ Constraints rows w

@[expose] def replace (i : ℕ) (r : Row) (w : Assignment) : Assignment :=
  Function.update w i (r w)

theorem constraints_cons (p : Row) (rows : List Row) (w : Assignment) :
    Constraints (p :: rows) w ↔ p w = 0 ∧ Constraints rows w := by
  simp [Constraints]

theorem constraints_map (rows : List Row) (f : Assignment → Assignment) (w : Assignment) :
    Constraints (rows.map (fun r => r ∘ f)) w ↔ Constraints rows (f w) := by
  simp [Constraints, Function.comp_def]

theorem constraints_congr (a b : List Row)
    (h : List.Forall₂ (fun f g => ∀ w, f w = 0 ↔ g w = 0) a b) :
    ∀ w, Constraints a w ↔ Constraints b w := by
  induction h with
  | nil => simp [Constraints]
  | @cons f g a b hfg hab ih =>
    intro w
    simp only [constraints_cons]
    exact and_congr (hfg w) (ih w)

theorem solutions_congr (a b : List Row)
    (h : ∀ w, Constraints a w ↔ Constraints b w) :
    ∀ q, HasSolution a q ↔ HasSolution b q := by
  intro q
  simp only [HasSolution, h]

theorem eliminate (p r : Row) (rows : List Row) (i : ℕ) (c : ℚ)
    (hi : i ≠ 0) (hc : c ≠ 0)
    (hp : ∀ w, p w = c * (w i - r w))
    (hr : ∀ w, r (replace i r w) = r w) :
    ∀ q, HasSolution (p :: rows) q ↔
      HasSolution (rows.map (fun f => f ∘ replace i r)) q := by
  intro q
  constructor
  · rintro ⟨w, hw, hs⟩
    obtain ⟨hpw, hrows⟩ := (constraints_cons p rows w).1 hs
    have hwi : w i = r w := by
      rw [hp] at hpw
      exact sub_eq_zero.mp ((mul_eq_zero.mp hpw).resolve_left hc)
    have hup : replace i r w = w := by
      simp [replace, ← hwi]
    exact ⟨w, hw, (constraints_map rows (replace i r) w).2 (hup.symm ▸ hrows)⟩
  · rintro ⟨w, hw, hs⟩
    refine ⟨replace i r w, ?_, (constraints_cons p rows _).2 ⟨?_, ?_⟩⟩
    · simpa [replace, Ne.symm hi] using hw
    · rw [hp, hr]
      simp [replace]
    · exact (constraints_map rows (replace i r) w).1 hs

@[expose] def shear (base : ℕ) (high : List ℕ) (sign : ℚ) (w : Assignment) : Assignment :=
  fun i => if i ∈ high then w i + sign * w base else w i

theorem shear_inverse (base : ℕ) (high : List ℕ) (hbase : base ∉ high)
    (sign : ℚ) (w : Assignment) :
    shear base high (-sign) (shear base high sign w) = w := by
  funext i
  by_cases hi : i ∈ high <;> simp [shear, hi, hbase]

theorem shear_zero (base : ℕ) (high : List ℕ) (hzero : 0 ∉ high)
    (sign : ℚ) (w : Assignment) : shear base high sign w 0 = w 0 := by
  simp [shear, hzero]

theorem shear_solutions (rows : List Row) (base : ℕ) (high : List ℕ)
    (hbase : base ∉ high) (hzero : 0 ∉ high) (sign : ℚ) :
    ∀ q, HasSolution rows q ↔
      HasSolution (rows.map (fun f => f ∘ shear base high sign)) q := by
  intro q
  constructor
  · rintro ⟨w, hw, hs⟩
    refine ⟨shear base high (-sign) w, ?_, ?_⟩
    · simpa [shear_zero base high hzero] using hw
    · apply (constraints_map rows _ _).2
      have heq := shear_inverse base high hbase (-sign) w
      simp only [neg_neg] at heq
      simpa only [heq] using hs
  · rintro ⟨w, hw, hs⟩
    exact ⟨shear base high sign w, (shear_zero base high hzero sign w).trans hw,
      (constraints_map rows _ _).1 hs⟩

theorem constraints_append (a b : List Row) (w : Assignment) :
    Constraints (a ++ b) w ↔ Constraints a w ∧ Constraints b w := by
  simp only [Constraints, List.mem_append]
  constructor
  · intro h; exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨ha,hb⟩ r (hr|hr)
    · exact ha r hr
    · exact hb r hr

theorem move_pivot (a b : List Row) (p : Row) :
    ∀ q, HasSolution (a ++ p :: b) q ↔ HasSolution (p :: (a ++ b)) q := by
  apply solutions_congr
  intro w
  simp only [constraints_append, constraints_cons]
  tauto

theorem replace_row (a b : List Row) (p r : Row)
    (h : ∀ w, Constraints (a ++ b) w → p w = r w) :
    ∀ q, HasSolution (a ++ p :: b) q ↔ HasSolution (a ++ r :: b) q := by
  apply solutions_congr
  intro w
  simp only [constraints_append, constraints_cons]
  constructor
  · rintro ⟨ha, hp, hb⟩
    exact ⟨ha, (h w ((constraints_append a b w).2 ⟨ha,hb⟩)).symm.trans hp, hb⟩
  · rintro ⟨ha, hr, hb⟩
    exact ⟨ha, (h w ((constraints_append a b w).2 ⟨ha,hb⟩)).trans hr, hb⟩


theorem finite_solution_iff {n : ℕ} (index : Fin (n+1) → ℕ)
    (hi : Function.Injective index) (hzero : index 0 = 0)
    (rows : List Row) (C : (Fin (n+1) → ℚ) → Prop)
    (heval : ∀ w, Constraints rows w ↔ C (fun j => w (index j))) (q : ℚ) :
    HasSolution rows q ↔ ∃ v : Fin n → ℚ, C (Fin.cons q v) := by
  constructor
  · rintro ⟨w, hw, hs⟩
    let v : Fin (n+1) → ℚ := fun j => w (index j)
    have hv : v 0 = q := by simpa [v, hzero] using hw
    refine ⟨Fin.tail v, ?_⟩
    have hc : C v := (heval w).1 hs
    simpa only [← hv, Fin.cons_self_tail] using hc
  · rintro ⟨v, hv⟩
    let u : Assignment := Function.extend index (Fin.cons q v) (fun _ => 0)
    have hu : ∀ j : Fin (n+1), u (index j) = (Fin.cons q v : Fin (n+1) → ℚ) j := by
      intro j
      exact hi.extend_apply (Fin.cons q v) (fun _ => 0) j
    refine ⟨u, ?_, (heval u).2 ?_⟩
    · simpa [hzero] using hu 0
    · simpa only [show (fun j => u (index j)) = Fin.cons q v from funext hu] using hv


@[expose] def gapOffset : List ℕ → ℕ → ℕ
  | [], _ => 0
  | h::t, n => (if h ≤ n then 1 else 0) + gapOffset t n

theorem gapOffset_mono (gaps : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    gapOffset gaps a ≤ gapOffset gaps b := by
  induction gaps with
  | nil => simp [gapOffset]
  | cons h t ih =>
    simp only [gapOffset]
    have hs : (if h ≤ a then 1 else 0) ≤ (if h ≤ b then 1 else 0) := by
      split_ifs <;> omega
    exact Nat.add_le_add hs ih

theorem gapIndex_strictMono (gaps : List ℕ) :
    StrictMono (fun n => n + gapOffset gaps n) := by
  intro a b hab
  change a + gapOffset gaps a < b + gapOffset gaps b
  have ho := gapOffset_mono gaps (Nat.le_of_lt hab)
  omega

theorem gapIndex_injective {n : ℕ} (gaps : List ℕ) :
    Function.Injective (fun j : Fin n => j.val + gapOffset gaps j.val) :=
  (gapIndex_strictMono gaps).injective.comp Fin.val_injective

end CircuitReplay
