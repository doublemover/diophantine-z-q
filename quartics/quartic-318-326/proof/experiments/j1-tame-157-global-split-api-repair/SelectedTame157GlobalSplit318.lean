module
public import SelectedCollisionHalfCost318
public import SelectedFiniteIntegerBudget318
public section
noncomputable section
open NumberField
open SelectedJOneExactMinorLoss318 SelectedFiniteIntegerBudget318
open scoped BigOperators

namespace SelectedTame157GlobalSplit318
variable {L : Type*} [Field L] [NumberField L]
variable (v : FinitePlace L) {g : ℕ}
variable (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
variable (u : Fin g → L) (hu : ∀ i, u i ≠ 0)
variable (I : Matrix (Fin g) (Fin g) (integralAt v))
variable (frames : baseMatrix v I = Matrix.diagonal u * m * C)

include hm hC hu I frames in
/-- Away from 157, the original actual dual section has only the
finite norm of 11M: no double charge of the 157 collision. -/
theorem away_exact_upper (M : ℕ) (hM : 0 < M) (h157 : v (157:L) = 1)
    (witness : ∀ i, ∃ t : L, v t ≤ 1 ∧ u i*t = -((1727*M:ℕ):L)) :
    -Real.log (v ((m.det*C.det)⁻¹)) ≤ (g:ℝ)*(-Real.log (v ((11*M:ℕ):L))) := by
  have hn : ((11*M:ℕ):L) ≠ 0 := by exact_mod_cast (show 11*M ≠ 0 by positivity)
  have hratio : v (-((1727*M:ℕ):L)) = v ((11*M:ℕ):L) := by
    have h : v (1727:L) = v (11:L) := by
      rw [show (1727:L) = (11:L)*157 by norm_num,map_mul,h157,mul_one]
    simp only [Nat.cast_mul,Nat.cast_ofNat,map_neg_eq_map,map_mul,h]
  have hcol (i : Fin g) : -Real.log (v (u i)) ≤ -Real.log (v ((11*M:ℕ):L)) := by
    obtain ⟨t,ht,hEq⟩ := witness i
    apply neg_le_neg
    apply Real.log_le_log (FinitePlace.pos_iff.mpr hn)
    rw [←hratio,←hEq,map_mul]
    exact mul_le_of_le_one_right (apply_nonneg v _) ht
  have h := exact_row v m C hm hC u hu I frames
  rw [h.2]
  calc
    _ ≤ ∑ i, -Real.log (v (u i)) := sub_le_self _ h.1
    _ ≤ ∑ _i : Fin g, -Real.log (v ((11*M:ℕ):L)) := Finset.sum_le_sum fun i _ => hcol i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

variable (M : ℕ) (V₀ V₁ : Finset (FinitePlace L)) (row : FinitePlace L → ℝ)

/-- Sum the disjoint blocks of the same actual finite support. At 157 use
the tame half-contact bound; elsewhere the existing actual dual witness.
The entire improvement is half log 157 per differential, and applies
only when 157 does not divide the literal level. -/
theorem split_budget [DecidableEq (FinitePlace L)] (hM : 0 < M) (disjoint : Disjoint V₀ V₁)
    (away : ∀ v ∈ V₀, row v ≤ (g:ℝ)*(-Real.log (v ((11*M:ℕ):L))))
    (near : ∀ v ∈ V₁, row v ≤ ((g:ℝ)/2)*(-Real.log (v (157:L)))) :
    (∑ v ∈ V₀ ∪ V₁, row v) / (Module.finrank ℚ L:ℝ) ≤
      (g:ℝ)*(Real.log (M:ℝ)+Real.log 11+Real.log 157/2) := by
  have hdim : 0 < (Module.finrank ℚ L:ℝ) := by
    exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have h₀ : (∑ v ∈ V₀, row v) / (Module.finrank ℚ L:ℝ) ≤
      (g:ℝ)*Real.log (11*(M:ℝ)) := by
    apply (div_le_iff₀ hdim).mpr
    calc
      _ ≤ ∑ v ∈ V₀, (g:ℝ)*(-Real.log (v ((11*M:ℕ):L))) := Finset.sum_le_sum away
      _ = (g:ℝ)*(∑ v ∈ V₀, -Real.log (v ((11*M:ℕ):L))) := by rw [Finset.mul_sum]
      _ ≤ (g:ℝ)*((Module.finrank ℚ L:ℝ)*Real.log ((11*M:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_left (natural_budget (L:=L) (11*M) (by positivity) V₀) (by positivity)
      _ = _ := by push_cast; ring
  have h₁ := aggregate_157 (L:=L) g V₁ row near
  rw [Finset.sum_union disjoint,add_div]
  calc
    _ ≤ (g:ℝ)*Real.log (11*(M:ℝ)) + ((g:ℝ)/2)*Real.log 157 := add_le_add h₀ h₁
    _ = _ := by rw [Real.log_mul (by norm_num : (11:ℝ) ≠ 0) hM']; ring

end SelectedTame157GlobalSplit318

#print axioms SelectedTame157GlobalSplit318.away_exact_upper
#print axioms SelectedTame157GlobalSplit318.split_budget
