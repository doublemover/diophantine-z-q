module
public import ActualPrimitiveResidueMap318
public section
noncomputable section
namespace FiniteImprimitiveCorrection318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {X : Type*} [DecidableEq X]

@[expose] def mass (S : Finset X) (w : X → ℝ) : ℝ := ∑x∈S,w x
@[expose] def event (S : Finset X) (w : X → ℝ) (E : X → Prop) [DecidablePred E] : ℝ :=
  ∑x∈S,if E x then w x else 0

lemma filter_mass_split (S : Finset X) (w : X → ℝ) (P : X → Prop) [DecidablePred P] :
    mass S w=mass (S.filter P) w+mass (S.filter (fun x => ¬P x)) w := by
  simp only [mass,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P x <;> simp only [h,ite_true,ite_false,not_true_eq_false,not_false_eq_true,add_zero,zero_add]

lemma filter_event_split (S : Finset X) (w : X → ℝ) (P E : X → Prop)
    [DecidablePred P] [DecidablePred E] :
    event S w E=event (S.filter P) w E+event (S.filter (fun x => ¬P x)) w E :=
  filter_mass_split S (fun x => if E x then w x else 0) P

lemma event_between (S : Finset X) (w : X → ℝ) (E : X → Prop) [DecidablePred E]
    (hw : ∀x∈S,0≤w x) : 0≤event S w E ∧ event S w E≤mass S w := by
  constructor
  · exact Finset.sum_nonneg (fun x hx => by split_ifs <;> first | exact hw x hx | exact le_rfl)
  · exact Finset.sum_le_sum (fun x hx => by split_ifs <;> first | exact le_rfl | exact hw x hx)

/-- Exact decomposition of the original remainder. The primitive local
density is NOT applied to imprimitive points without retaining the error. -/
theorem exact_imprimitive_correction (S : Finset X) (w : X → ℝ) (P E : X → Prop)
    [DecidablePred P] [DecidablePred E] (ν : ℝ) :
    event S w E-ν*mass S w=
      (event (S.filter P) w E-ν*mass (S.filter P) w)+
      (event (S.filter (fun x => ¬P x)) w E-ν*mass (S.filter (fun x => ¬P x)) w) := by
  rw [filter_event_split S w P E,filter_mass_split S w P]
  ring

/-- A genuine uniform bound on the imprimitive correction: its actual
weighted mass, not a supplied missing-density hypothesis. -/
theorem actual_imprimitive_error_bound (S : Finset X) (w : X → ℝ) (P E : X → Prop)
    [DecidablePred P] [DecidablePred E] (ν : ℝ) (hν : 0≤ν) (hν1 : ν≤1)
    (hw : ∀x∈S,0≤w x) :
    |event S w E-ν*mass S w|≤
      |event (S.filter P) w E-ν*mass (S.filter P) w|+
        mass (S.filter (fun x => ¬P x)) w := by
  have hb := event_between (S.filter (fun x => ¬P x)) w E
    (fun x hx => hw x (Finset.mem_filter.mp hx).1)
  have hm : 0≤mass (S.filter (fun x => ¬P x)) w :=
    Finset.sum_nonneg (fun x hx => hw x (Finset.mem_filter.mp hx).1)
  have hn := mul_nonneg hν hm
  have hu := mul_le_mul_of_nonneg_right hν1 hm
  have hi : |event (S.filter (fun x => ¬P x)) w E-
      ν*mass (S.filter (fun x => ¬P x)) w|≤mass (S.filter (fun x => ¬P x)) w := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hb.1,hb.2,hn,hu]
  rw [exact_imprimitive_correction S w P E]
  exact (abs_add_le _ _).trans (add_le_add_left hi _)

end FiniteImprimitiveCorrection318
