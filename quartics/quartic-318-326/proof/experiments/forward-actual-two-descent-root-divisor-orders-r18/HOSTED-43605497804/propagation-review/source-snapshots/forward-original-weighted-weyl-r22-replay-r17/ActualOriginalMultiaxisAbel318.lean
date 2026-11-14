module
public import ActualOriginalAxisRectangle318
public section
noncomputable section
namespace ActualOriginalMultiaxisAbel318
open ActualOriginalIteratedDifference318 ActualOriginalMixedTranslation318
open ActualOriginalAxisRectangle318 ActualOriginalFiniteAbel318
open scoped BigOperators

/-- Iterated Abel consumes ALL mixed orders, not just coordinatewise
first variation. Each axis contributes its own prefix cap and factor1+R.
The same weight remains inside the full rectangle until its actual finite
differences are bounded. -/
theorem actual_multiaxis_abel {E : Type*} [AddCommMonoid E]
    (admissible : E → Prop) (ρ R : ℝ) (hρ : 0≤ρ) (hR : 0≤R)
    (as : List (Axis E)) :
    ∀ g : E → ℂ, ∀ C : ℝ, 0≤C →
    (∀ a∈as, 0≤a.cap ∧ admissible a.step ∧ (a.steps : ℝ)*ρ≤R ∧
      ∀ n≤a.steps+1, ‖prefix a.phase n‖≤a.cap) →
    (∀ us : List E, us.length≤as.length → (∀ u∈us, admissible u) →
      ∀ x, ‖mixedDifference g us x‖≤C*ρ^us.length) →
    ∀ x, ‖axisRectangle g as x‖≤C*(1+R)^as.length*axisCapProduct as := by
  induction as with
  | nil =>
    intro g C hC ha hb x
    have hh := hb [] (by simp) (by simp) x
    simpa only [List.length_nil,mixedDifference,axisRectangle,axisCapProduct,pow_zero,mul_one] using hh
  | cons a as ih =>
    intro g C hC ha hb x
    obtain ⟨hcap,had,hsize,hprefix⟩ := ha a List.mem_cons_self
    have hat := fun b hmem => ha b (List.mem_cons_of_mem a hmem)
    have hT : 0≤(1+R)^as.length*axisCapProduct as :=
      mul_nonneg (pow_nonneg (by linarith) _) (actual_axis_cap_product_nonneg as (fun b hb => (hat b hb).1))
    have hbase (y : E) : ‖axisRectangle g as y‖≤C*(1+R)^as.length*axisCapProduct as := by
      apply ih g C hC hat
      intro us hu hads z
      apply hb us (by simp only [List.length_cons]; omega) hads z
    have hdelta (y : E) :
        ‖axisRectangle (fun z => g (z+a.step)-g z) as y‖≤
          (C*ρ)*(1+R)^as.length*axisCapProduct as := by
      apply ih _ (C*ρ) (mul_nonneg hC hρ) hat
      intro us hu hads z
      rw [actual_mixed_step]
      have hh := hb (a.step::us) (by simp only [List.length_cons]; omega)
        (by
          intro u hu'
          rcases List.mem_cons.mp hu' with he | he
          · simpa only [he] using had
          · exact hads u he) z
      convert hh using 1 <;> simp only [List.length_cons,pow_succ] <;> ring
    let F : ℕ → ℂ := fun j => axisRectangle g as (x+j • a.step)
    have hinc (j : ℕ) : ‖F j-F (j+1)‖≤(C*ρ)*(1+R)^as.length*axisCapProduct as := by
      have he : x+(j+1) • a.step=(x+j • a.step)+a.step := by
        simp only [add_nsmul,one_nsmul,add_assoc]
      have hh := hdelta (x+j • a.step)
      rw [actual_rectangle_step] at hh
      simpa only [F,he,norm_sub_rev] using hh
    have hvar : variation F a.steps≤C*(1+R)^(as.length+1)*axisCapProduct as := by
      calc
        _ ≤ C*(1+R)^as.length*axisCapProduct as+
            ∑ j∈Finset.range a.steps, (C*ρ)*(1+R)^as.length*axisCapProduct as := by
          exact add_le_add (hbase _) (Finset.sum_le_sum (fun j hj => hinc j))
        _ = C*((1+R)^as.length*axisCapProduct as)*(1+(a.steps : ℝ)*ρ) := by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
          ring
        _ ≤ C*((1+R)^as.length*axisCapProduct as)*(1+R) :=
          mul_le_mul_of_nonneg_left (add_le_add_left hsize 1) (mul_nonneg hC hT)
        _ = _ := by rw [pow_succ]; ring
    change ‖weightedPrefix a.phase F (a.steps+1)‖≤_
    apply (actual_finite_abel_bound a.phase F a.steps a.cap hprefix).trans
    apply (mul_le_mul_of_nonneg_left hvar hcap).trans_eq
    simp only [List.length_cons,axisCapProduct]
    ring

end ActualOriginalMultiaxisAbel318
