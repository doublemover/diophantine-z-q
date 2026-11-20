module
public import SelectedSameWitnessFinitePipeline318
public import SelectedCollisionHalfCost318
public import SelectedFiniteIntegerBudget318
public section
noncomputable section
open NumberField SelectedJOneExactMinorLoss318 SelectedFiniteIntegerBudget318
open scoped BigOperators

namespace SelectedSameWitnessGlobalBudget318
variable {L : Type*} [Field L] [NumberField L]

@[expose] def finiteLog (v : FinitePlace L) (x : L) := -Real.log (v x)

private theorem log_fallback (v : FinitePlace L) {M : ℕ} (hM : 0 < M) :
    finiteLog v (-((1727:L)*(M:L))) = finiteLog v (M:L) + finiteLog v (1727:L) := by
  have hM' : (M:L) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have h1727 : (1727:L) ≠ 0 := by norm_num
  unfold finiteLog
  rw [map_neg_eq_map,map_mul,Real.log_mul
    (FinitePlace.pos_iff.mpr h1727).ne' (FinitePlace.pos_iff.mpr hM').ne']
  ring

private theorem total_mask [DecidableEq (FinitePlace L)] (V A : Finset (FinitePlace L))
    (hA : A ⊆ V) (f : FinitePlace L → ℝ) :
    (∑ v ∈ V, if v ∈ A then f v else 0) = ∑ v ∈ A, f v := by
  have hv : V.filter (fun v => v ∈ A) = A := by
    ext v
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h,h⟩⟩
  rw [← Finset.sum_filter,hv]

/-- Tame contact on the actual coefficient in the same chosen frame.
A change by an actual integral unit may be incorporated in d. -/
theorem tame_cost_of_contact (v : FinitePlace L) {g M : ℕ}
    (u x c d : Fin g → L) (hMunit : v (M:L) = 1) (h11 : v (11:L) = 1)
    (hc : ∀ i, v (c i) = 1) (hd : ∀ i, v (d i) = 1)
    (contact : ∀ i, -(1727:L) = c i*(x i)^2)
    (differential : ∀ i, u i = d i*x i) :
    v (M:L) = 1 ∧ (∀ i, u i ≠ 0) ∧
      (∀ i, finiteLog v (u i) = finiteLog v (157:L)/2) := by
  refine ⟨hMunit, ?_, ?_⟩
  · intro i
    have hd' : d i ≠ 0 := by
      intro h
      have hm := hd i
      rw [h,map_zero] at hm
      norm_num at hm
    have hx' : x i ≠ 0 := by
      intro h
      have hm := contact i
      rw [h] at hm
      norm_num at hm
    rw [differential i]
    exact mul_ne_zero hd' hx'
  · intro i
    exact SelectedCollisionHalfCost318.contact_157 v (hc i) (hd i) h11 (contact i)
      (differential i)

section FiniteSupport
variable [DecidableEq (FinitePlace L)]
variable {g : ℕ} (m : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0)
variable (C : FinitePlace L → Matrix (Fin g) (Fin g) L) (hC : ∀ v, (C v).det ≠ 0)
variable (u : FinitePlace L → Fin g → L)
variable (I : (v : FinitePlace L) → Matrix (Fin g) (Fin g) (integralAt v))
variable (frames : ∀ v, baseMatrix v (I v) = Matrix.diagonal (u v) * m * C v)
variable (M : ℕ) (hM : 0 < M)
variable (V T W : Finset (FinitePlace L)) (hT : T ⊆ V) (hW : W ⊆ V)
variable (hTW : Disjoint T W)

local notation "q" => fun v => (m.det*(C v).det)⁻¹
local notation "d" => fun v => (baseMatrix v (I v)).det
local notation "D" => (Module.finrank ℚ L:ℝ)

/-- Both masks are attached to one actual ordered minor and one actual
integral matrix at each place. Outside the two masks one uses the
noncollision M estimate from the genuine same-witness pipeline. At T
one uses the actual dz-frame contact estimate in the same row scalar u,
and at W one needs an actual integral dual witness for -1727M; no
wild model is supplied by selecting W. -/
include hm hC frames hM hT hW hTW in
theorem finite_budget
    (noncollision : ∀ v ∈ V, v ∉ T → v ∉ W →
      finiteLog v (q v) ≤ (g:ℝ)*finiteLog v (M:L) - finiteLog v (d v))
    (tame : ∀ v ∈ T, v (M:L) = 1 ∧
      (∀ i, u v i ≠ 0) ∧ (∀ i, finiteLog v (u v i) = finiteLog v (157:L)/2))
    (fallback : ∀ v ∈ W, ∀ i, ∃ t : integralAt v,
      u v i * algebraMap (integralAt v) L t = -((1727:L)*(M:L))) :
    ((∑ v ∈ V, finiteLog v (q v)) + ∑ v ∈ V, finiteLog v (d v)) / D ≤
      (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) +
        (∑ v ∈ W, finiteLog v (1727:L)) + (∑ v ∈ T, finiteLog v (157:L))/2) / D := by
  have hb (v) (hv : v ∈ V) :
      finiteLog v (q v) + finiteLog v (d v) ≤
        (g:ℝ)*(finiteLog v (M:L) +
          (if v ∈ W then finiteLog v (1727:L) else 0) +
          (if v ∈ T then finiteLog v (157:L) else 0)/2) := by
    by_cases ht : v ∈ T
    · have hw : v ∉ W := fun hw => (Finset.disjoint_left.mp hTW) ht hw
      obtain ⟨hunit,hu,hHalf⟩ := tame v ht
      have he := (exact_row v m (C v) hm (hC v) (u v) hu (I v) (frames v)).2
      change finiteLog v (q v) = (∑ i, finiteLog v (u v i)) - finiteLog v (d v) at he
      rw [he]
      simp only [ht,hw,if_true,if_false,sub_add_cancel]
      simp_rw [hHalf]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hzero : finiteLog v (M:L) = 0 := by unfold finiteLog; rw [hunit,Real.log_one,neg_zero]
      rw [hzero]
      exact le_of_eq (by ring)
    · by_cases hw : v ∈ W
      · have ha : (-((1727:L)*(M:L))) ≠ 0 := by
          have hm' : (M:L) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
          exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hm')
        have he := SelectedBadLevelLocalDerivative318.one_place_budget v m (C v) hm (hC v)
          (u v) (I v) (frames v) (-((1727:L)*(M:L))) ha (fallback v hw)
        change finiteLog v (q v) ≤
          (g:ℝ)*finiteLog v (-((1727:L)*(M:L))) - finiteLog v (d v) at he
        rw [log_fallback v hM] at he
        simpa only [ht,hw,if_true,if_false,zero_div,add_zero] using (le_sub_iff_add_le.mp he)
      · simpa only [ht,hw,if_false,zero_div,add_zero] using
          (le_sub_iff_add_le.mp (noncollision v hv ht hw))
  have hsum := Finset.sum_le_sum (fun v hv => hb v hv)
  simp only [← Finset.sum_add_distrib] at ⊢
  refine div_le_div_of_nonneg_right (hsum.trans_eq ?_) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_div,
    total_mask V W hW,total_mask V T hT]

/-- Genuine all-finite degree of the same minor, conditional also on
the actual finite-support unit identities for that minor and its loss.
This is first a support-sensitive inequality rather than a rational
integer upper bound; the loss is charged with the same sign throughout. -/
include hm hC frames hM hT hW hTW in
theorem degree_budget
    (noncollision : ∀ v ∈ V, v ∉ T → v ∉ W →
      finiteLog v (q v) ≤ (g:ℝ)*finiteLog v (M:L) - finiteLog v (d v))
    (tame : ∀ v ∈ T, v (M:L) = 1 ∧
      (∀ i, u v i ≠ 0) ∧ (∀ i, finiteLog v (u v i) = finiteLog v (157:L)/2))
    (fallback : ∀ v ∈ W, ∀ i, ∃ t : integralAt v,
      u v i * algebraMap (integralAt v) L t = -((1727:L)*(M:L)))
    (offQ : ∀ v ∉ V, v (q v) = 1) (offD : ∀ v ∉ V, v (d v) = 1) :
    degree q + degree d ≤
      (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) +
        (∑ v ∈ W, finiteLog v (1727:L)) + (∑ v ∈ T, finiteLog v (157:L))/2) / D := by
  rw [degree_eq_finset V q offQ,degree_eq_finset V d offD,← add_div]
  exact finite_budget m hm C hC u I frames M hM V T W hT hW hTW noncollision tame fallback

end FiniteSupport

section RationalBounds
variable (g M : ℕ) (hM : 0 < M)
variable (V T W : Finset (FinitePlace L))
local notation "D" => (Module.finrank ℚ L:ℝ)

/-- If the genuine 157-unit condition holds on all fallback places,
the only 157 contribution is the exact half-contact block. The shape
works even if L ramifies or splits at 157. -/
include hM in
theorem off_level_157_bound (fallbackAway : ∀ v ∈ W, v (157:L) = 1) :
    (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) +
      (∑ v ∈ W, finiteLog v (1727:L)) + (∑ v ∈ T, finiteLog v (157:L))/2) / D ≤
      (g:ℝ)*(Real.log (M:ℝ) + Real.log 11 + Real.log 157/2) := by
  have hdim : 0 < D := by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  have hswap : (∑ v ∈ W, finiteLog v (1727:L)) = ∑ v ∈ W, finiteLog v (11:L) := by
    apply Finset.sum_congr rfl
    intro v hv
    unfold finiteLog
    rw [show (1727:L) = (11:L)*157 by norm_num,map_mul,fallbackAway v hv,mul_one]
  have h₀ : (∑ v ∈ V, finiteLog v (M:L)) ≤ D * Real.log (M:ℝ) :=
    natural_budget M hM V
  have h₁ : (∑ v ∈ W, finiteLog v (11:L)) ≤ D * Real.log 11 :=
    natural_budget 11 (by decide) W
  have h₂ : (∑ v ∈ T, finiteLog v (157:L)) ≤ D * Real.log 157 :=
    natural_budget 157 (by decide) T
  rw [hswap]
  apply (div_le_iff₀ hdim).mpr
  calc
    _ ≤ (g:ℝ)*(D*Real.log (M:ℝ) + D*Real.log 11 + (D*Real.log 157)/2) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₀ h₁)
        (div_le_div_of_nonneg_right h₂ (by norm_num))) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- If 157 divides the literal level, use no tame 157 charge; the
original full collision witness then contributes at most log 1727.
No local case is inferred from the value of M by this estimate. -/
include hM in
theorem no_tame_bound :
    (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) + (∑ v ∈ W, finiteLog v (1727:L))) / D ≤
      (g:ℝ)*(Real.log (M:ℝ) + Real.log 1727) := by
  have hdim : 0 < D := by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  have h₀ : (∑ v ∈ V, finiteLog v (M:L)) ≤ D * Real.log (M:ℝ) :=
    natural_budget M hM V
  have h₁ : (∑ v ∈ W, finiteLog v (1727:L)) ≤ D * Real.log 1727 :=
    natural_budget 1727 (by decide) W
  apply (div_le_iff₀ hdim).mpr
  calc
    _ ≤ (g:ℝ)*(D*Real.log (M:ℝ) + D*Real.log 1727) :=
      mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (Nat.cast_nonneg _)
    _ = _ := by ring

end RationalBounds
end SelectedSameWitnessGlobalBudget318

#print axioms SelectedSameWitnessGlobalBudget318.tame_cost_of_contact
#print axioms SelectedSameWitnessGlobalBudget318.finite_budget
#print axioms SelectedSameWitnessGlobalBudget318.degree_budget
#print axioms SelectedSameWitnessGlobalBudget318.off_level_157_bound
#print axioms SelectedSameWitnessGlobalBudget318.no_tame_bound
