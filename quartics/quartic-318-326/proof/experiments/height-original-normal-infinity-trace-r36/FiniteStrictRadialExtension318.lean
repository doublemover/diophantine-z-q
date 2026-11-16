module
public import Mathlib.Tactic
public section
noncomputable section
namespace FiniteStrictRadialExtension318

/-- One strict linear inequality admits a uniform positive radial interval.
The negative-coefficient case is retained instead of dividing by it. -/
theorem one_slack (a c : ℝ) (h : a<c) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t : ℝ, 0≤t → t≤δ → a+t*a<c := by
  by_cases ha : a≤0
  · refine ⟨1,by norm_num,?_⟩
    intro t ht _
    have hm := mul_nonpos_of_nonneg_of_nonpos ht ha
    linarith
  · have hp : 0<a := lt_of_not_ge ha
    refine ⟨(c-a)/(2*a),div_pos (sub_pos.mpr h) (by positivity),?_⟩
    intro t ht hδ
    have hm := (le_div_iff₀ (by positivity : 0<2*a)).mp hδ
    nlinarith

/-- A finite family is controlled on the same entire positive radial
interval; this is the missing quantifier in pointwise slack arguments. -/
theorem finite_slack {ι : Type*} (s : Finset ι) (a c : ι → ℝ)
    (h : ∀ i∈s, a i<c i) :
    ∃ δ : ℝ, 0<δ ∧ ∀ i∈s, ∀ t : ℝ, 0≤t → t≤δ → a i+t*a i<c i := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    intro h
    obtain ⟨δ,hδ,hall⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨ε,hε,hone⟩ := one_slack (a i) (c i) (h i (Finset.mem_insert_self i s))
    refine ⟨min δ ε,lt_min hδ hε,?_⟩
    intro j hj t ht htδ
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hone t ht (le_trans htδ (min_le_right _ _))
    · exact hall j hj t ht (le_trans htδ (min_le_left _ _))
end FiniteStrictRadialExtension318
