module
public import ThreeJDerivativeOpen318
public import Mathlib.Analysis.Real.Sqrt
public section
noncomputable section
namespace ThreeJRamificationParameters318
open ThreeCompactParameter318 ThreeJEllipticOrders318
set_option maxHeartbeats 1000000

@[expose] def rootPlus : ℂ := 243+162*(Real.sqrt 3:ℝ)
@[expose] def rootMinus : ℂ := 243-162*(Real.sqrt 3:ℝ)

lemma sqrt_three_square : ((Real.sqrt 3:ℝ):ℂ)^2=3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
lemma sqrt_three_ne_zero : ((Real.sqrt 3:ℝ):ℂ) ≠ 0 := by
  intro h
  have := sqrt_three_square
  rw [h] at this
  norm_num at this

lemma D_factorization (t : ℂ) : D t=(t-rootPlus)*(t-rootMinus) := by
  unfold D rootPlus rootMinus
  linear_combination 26244*sqrt_three_square

lemma roots_distinct : rootPlus ≠ rootMinus := by
  intro h
  apply sqrt_three_ne_zero
  unfold rootPlus rootMinus at h
  linear_combination h/324

lemma D_rootPlus : D rootPlus=0 := by rw [D_factorization,sub_self,zero_mul]
lemma D_rootMinus : D rootMinus=0 := by rw [D_factorization,sub_self,mul_zero]
lemma rootPlus_ne_zero : rootPlus ≠ 0 := root_ne_zero D_rootPlus
lemma rootMinus_ne_zero : rootMinus ≠ 0 := root_ne_zero D_rootMinus
lemma rootPlus_ne_neg243 : rootPlus ≠ -243 := by
  intro h
  have := D_rootPlus
  rw [h] at this
  norm_num [D] at this
lemma rootMinus_ne_neg243 : rootMinus ≠ -243 := by
  intro h
  have := D_rootMinus
  rw [h] at this
  norm_num [D] at this

theorem D_zero_iff (t : ℂ) : D t=0 ↔ t=rootPlus ∨ t=rootMinus := by
  rw [D_factorization,mul_eq_zero,sub_eq_zero,sub_eq_zero]

/-- These are all finite ramified parameters for the exact original map,
including the finite cusp; the reciprocal origin is unramified. -/
@[expose] def multiplicity (t : ℂ) : ℕ :=
  (if t=0 then 2 else 0)+(if t= -243 then 2 else 0)+
  (if t=rootPlus then 1 else 0)+(if t=rootMinus then 1 else 0)

lemma multiplicity_zero : multiplicity 0=2 := by
  simp [multiplicity,Ne.symm rootPlus_ne_zero,Ne.symm rootMinus_ne_zero]
lemma multiplicity_neg243 : multiplicity (-243)=2 := by
  simp [multiplicity,Ne.symm rootPlus_ne_neg243,Ne.symm rootMinus_ne_neg243]
lemma multiplicity_rootPlus : multiplicity rootPlus=1 := by
  simp [multiplicity,rootPlus_ne_zero,rootPlus_ne_neg243,roots_distinct]
lemma multiplicity_rootMinus : multiplicity rootMinus=1 := by
  simp [multiplicity,rootMinus_ne_zero,rootMinus_ne_neg243,Ne.symm roots_distinct]

theorem multiplicity_local_degree {t : ℂ} (ht : t ≠ 0) :
    multiplicity t+1=ThreeJOrdinaryOrders318.finiteOrder t := by
  by_cases h243 : t= -243
  · subst t
    rw [multiplicity_neg243]
    simp [ThreeJOrdinaryOrders318.finiteOrder]
  · by_cases hp : t=rootPlus
    · subst t
      rw [multiplicity_rootPlus]
      simp [ThreeJOrdinaryOrders318.finiteOrder,rootPlus_ne_neg243,D_rootPlus]
    · by_cases hm : t=rootMinus
      · subst t
        rw [multiplicity_rootMinus]
        simp [ThreeJOrdinaryOrders318.finiteOrder,rootMinus_ne_neg243,D_rootMinus]
      · have hd : D t ≠ 0 := by
          intro hd0
          exact (not_or.mpr ⟨hp,hm⟩) (D_zero_iff.mp hd0)
        simp [multiplicity,ht,h243,hp,hm,ThreeJOrdinaryOrders318.finiteOrder,hd]

theorem multiplicity_nonzero_iff (t : ℂ) :
    multiplicity t ≠ 0 ↔ t=0 ∨ t= -243 ∨ t=rootPlus ∨ t=rootMinus := by
  unfold multiplicity
  split_ifs <;> simp_all

end ThreeJRamificationParameters318
