module
public import ActualOriginalPrimitiveSingularSeries318
public section
noncomputable section
namespace ActualOriginalPositiveRealPoint318
open QuadricCRTAssembly318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def originalForm (γ : ℝ) (x : Coordinates ℝ) : ℝ :=
  x.1.1^2+x.1.2^2+γ*x.2.2^2
@[expose] def point (κ T : ℝ) : Coordinates ℝ :=
  ((T^2+κ,0),(T^2-κ,0),2*T)

/-- The original five coordinates, not a quotient or shifted chart. -/
lemma point_on_original_quadric (κ T : ℝ) : equation κ (point κ T)=0 := by
  dsimp [equation,point]
  ring
lemma original_form_decomposition (κ T G γ : ℝ) :
    originalForm γ (point κ T)=
      T^2*(T^2-4*G)+κ^2+2*κ*T^2+4*(γ+G)*T^2 := by
  dsimp [originalForm,point]
  ring
lemma original_form_pos (κ T G γ : ℝ) (hκ : 0<κ) (hT : 0<T)
    (hlarge : 4*G<T^2) (hγ : -G≤γ) : 0<originalForm γ (point κ T) := by
  rw [original_form_decomposition κ T G γ]
  have hsq : 0<T^2 := sq_pos_of_pos hT
  have hlead : 0<T^2*(T^2-4*G) := mul_pos hsq (sub_pos.mpr hlarge)
  have hterm : 0≤2*κ*T^2 := by positivity
  have hlast : 0≤4*(γ+G)*T^2 := by
    have : 0≤γ+G := by linarith
    positivity
  nlinarith [sq_nonneg κ]

variable {J : Type*} [Fintype J]
@[expose] def gammaBudget (γ : J→ℝ) : ℝ := ∑j,|γ j|
@[expose] def chosenParameter (κ : ℝ) (γ : J→ℝ) : ℝ := κ+4*gammaBudget γ+2
lemma gammaBudget_nonneg (γ : J→ℝ) : 0≤gammaBudget γ :=
  Finset.sum_nonneg (fun j _ => abs_nonneg (γ j))
lemma gamma_lower (γ : J→ℝ) (j : J) : -gammaBudget γ≤γ j := by
  classical
  have h := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => abs_nonneg (γ i))
    (Finset.mem_univ j)
  have hj := neg_abs_le (γ j)
  dsimp [gammaBudget]
  linarith
lemma chosen_parameter_bounds (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    0<chosenParameter κ γ ∧ κ<(chosenParameter κ γ)^2 ∧
      4*gammaBudget γ<(chosenParameter κ γ)^2 := by
  have hG := gammaBudget_nonneg γ
  have hT : 1<chosenParameter κ γ := by dsimp [chosenParameter];linarith
  have hs : chosenParameter κ γ<(chosenParameter κ γ)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hT) (lt_trans (by norm_num : (0:ℝ)<1) hT)]
  dsimp [chosenParameter] at *
  constructor
  · linarith
  constructor <;> linarith

/-- One produced original smooth real point simultaneously makes every
specified original prime form positive, for any finite list of coefficients. -/
theorem actual_positive_real_point (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃x : Coordinates ℝ, equation κ x=0 ∧ 0<x.1.1 ∧ 0<x.2.1.1 ∧
      0<x.2.2 ∧ (∀j,0<originalForm (γ j) x) ∧
      ActualQuadricTaylor318.gradient κ x 0≠0 := by
  let T := chosenParameter κ γ
  obtain ⟨hT,hκT,hGT⟩ := chosen_parameter_bounds κ hκ γ
  have ha : 0<T^2+κ := by positivity
  refine ⟨point κ T,point_on_original_quadric κ T,ha,?_,?_,?_,?_⟩
  · change 0<T^2-κ
    exact sub_pos.mpr hκT
  · change 0<2*T
    exact mul_pos (by norm_num) hT
  · intro j
    exact original_form_pos κ T (gammaBudget γ) (γ j) hκ hT hGT (gamma_lower γ j)
  · change 2*(T^2+κ)≠0
    exact ne_of_gt (mul_pos (by norm_num) ha)

end ActualOriginalPositiveRealPoint318
