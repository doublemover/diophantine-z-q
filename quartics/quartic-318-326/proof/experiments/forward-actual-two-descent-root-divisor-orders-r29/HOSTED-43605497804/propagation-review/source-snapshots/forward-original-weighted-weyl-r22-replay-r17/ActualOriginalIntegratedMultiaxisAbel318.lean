module
public import ActualOriginalJointPrefixControl318
public section
noncomputable section
namespace ActualOriginalIntegratedMultiaxisAbel318
open MeasureTheory ActualOriginalFiniteIntegralTriangle318 ActualOriginalJointPrefixControl318
open ActualOriginalIteratedDifference318 ActualOriginalMixedTranslation318 ActualOriginalFiniteAbel318
open scoped BigOperators

/-- Integrated multiaxis Abel consumes JOINT prefix integrals one by
one. The arbitrary spatial weight stays nonseparable; all terminal and
mixed-difference terms are retained. Integrability is proved together
with the bound, so no undefined-integral convention is used. -/
theorem actual_integrated_multiaxis_abel {E : Type*} [AddCommMonoid E]
    (μ : Measure ℝ) (admissible : E → Prop) (ρ R M : ℝ)
    (hρ : 0≤ρ) (hR : 0≤R) (hM : 0≤M) (as : List (TimeAxis E)) :
    ∀ g : E → ℂ, ∀ C : ℝ, 0≤C →
    (∀ a∈as, admissible a.step ∧ (a.steps : ℝ)*ρ≤R) →
    (∀ us : List E, us.length≤as.length → (∀ u∈us, admissible u) →
      ∀ x, ‖mixedDifference g us x‖≤C*ρ^us.length) →
    ∀ F : ℝ → ℂ, JointPrefixControl μ M as F → ∀ x,
      Integrable (fun t => F t*timeRectangle g as x t) μ ∧
      (∫ t, ‖F t*timeRectangle g as x t‖ ∂μ)≤C*(1+R)^as.length*M := by
  induction as with
  | nil =>
    intro g C hC ha hb F hF x
    obtain ⟨hi,hm⟩ := hF
    have hg := hb [] (by simp) (by simp) x
    simp only [mixedDifference,List.length_nil,pow_zero,mul_one] at hg
    refine ⟨hi.mul_const (g x),?_⟩
    simp only [timeRectangle,List.length_nil,pow_zero,mul_one,norm_mul]
    rw [integral_mul_const]
    calc
      _ ≤ M*‖g x‖ := mul_le_mul_of_nonneg_right hm (norm_nonneg _)
      _ ≤ M*C := mul_le_mul_of_nonneg_left hg hM
      _ = _ := mul_comm _ _
  | cons a as ih =>
    intro g C hC ha hb F hF x
    obtain ⟨had,hsize⟩ := ha a List.mem_cons_self
    have hat := fun b hb' => ha b (List.mem_cons_of_mem a hb')
    have hbase (n : ℕ) (hn : n≤a.steps+1) (y : E) :=
      ih g C hC hat (fun us hu hads z => hb us (by simp only [List.length_cons]; omega) hads z)
        (fun t => F t*prefix (fun j => a.phase j t) n) (hF n hn) y
    have hdelta : ∀ us : List E, us.length≤as.length → (∀ u∈us, admissible u) →
        ∀ z, ‖mixedDifference (fun z => g z-g (z+a.step)) us z‖≤(C*ρ)*ρ^us.length := by
      intro us hu hads z
      rw [actual_mixed_sub,actual_mixed_translation,norm_sub_rev]
      have hh := hb (a.step::us) (by simp only [List.length_cons]; omega)
        (by
          intro u hu'
          rcases List.mem_cons.mp hu' with he | he
          · simpa only [he] using had
          · exact hads u he) z
      change ‖mixedDifference g us (z+a.step)-mixedDifference g us z‖≤_ at hh
      convert hh using 1 <;> simp only [List.length_cons,pow_succ] <;> ring
    let T : ℝ → ℂ := fun t => (F t*prefix (fun j => a.phase j t) (a.steps+1))*
      timeRectangle g as (x+a.steps • a.step) t
    let U : ℕ → ℝ → ℂ := fun j t => (F t*prefix (fun k => a.phase k t) (j+1))*
      timeRectangle (fun z => g z-g (z+a.step)) as (x+j • a.step) t
    have hT := hbase (a.steps+1) le_rfl (x+a.steps • a.step)
    have hU (j : ℕ) (hj : j∈Finset.range a.steps) : Integrable (U j) μ ∧
        (∫ t, ‖U j t‖ ∂μ)≤(C*ρ)*(1+R)^as.length*M := by
      have hn : j+1≤a.steps+1 := by have := Finset.mem_range.mp hj; omega
      exact ih _ (C*ρ) (mul_nonneg hC hρ) hat hdelta
        (fun t => F t*prefix (fun k => a.phase k t) (j+1)) (hF (j+1) hn) (x+j • a.step)
    have he : (fun t => F t*timeRectangle g (a::as) x t)=
        fun t => T t+∑ j∈Finset.range a.steps, U j t := by
      funext t
      have hh := actual_finite_abel (fun j => a.phase j t)
        (fun j => timeRectangle g as (x+j • a.step) t) a.steps
      change timeRectangle g (a::as) x t=_ at hh
      rw [hh,mul_add,Finset.mul_sum]
      dsimp only [T,U]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [actual_time_rectangle_backward]
        have hp : x+(j+1) • a.step=(x+j • a.step)+a.step := by
          simp only [add_nsmul,one_nsmul,add_assoc]
        rw [hp]
        ring
    have hiU := integrable_finsetSum (Finset.range a.steps) (fun j hj => (hU j hj).1)
    refine ⟨by rw [he]; exact hT.1.add hiU,?_⟩
    rw [he]
    calc
      _ ≤ (∫ t, ‖T t‖ ∂μ)+(∫ t, ‖∑ j∈Finset.range a.steps, U j t‖ ∂μ) :=
        actual_integral_norm_add μ T _ hT.1 hiU
      _ ≤ C*(1+R)^as.length*M+∑ j∈Finset.range a.steps, (∫ t, ‖U j t‖ ∂μ) :=
        add_le_add hT.2 (actual_integral_norm_sum μ _ U (fun j hj => (hU j hj).1))
      _ ≤ C*(1+R)^as.length*M+∑ j∈Finset.range a.steps, (C*ρ)*(1+R)^as.length*M :=
        add_le_add_left (Finset.sum_le_sum (fun j hj => (hU j hj).2)) _
      _ = C*(1+R)^as.length*M*(1+(a.steps : ℝ)*ρ) := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        ring
      _ ≤ C*(1+R)^as.length*M*(1+R) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hsize 1) (by positivity)
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

end ActualOriginalIntegratedMultiaxisAbel318
