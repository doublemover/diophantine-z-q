module
public import ScaledDetectorChain318
public import UniformPoleDomain318
public section
noncomputable section
namespace UniformScaledPoleDomain318
open Filter Set CircuitReplay ContactChainReal318 ContactWeightWitness318 ScaledContactWeights318 ScaledDetectorChain318
open scoped Topology

@[expose] def weights (c t : ℚ) : ℝ × ℝ × ℝ :=
  ((scaledWeight c t:ℝ),(((scaledWeight c t)^7*(delta c t)^18:ℚ):ℝ),
    (((scaledWeight c t)^25*(delta c t)^72:ℚ):ℝ))

lemma weights_limit (c : ℚ) (hc : c≠0) : Tendsto (weights c) atTop (𝓝 (0,0,0)) := by
  have he := Rat.continuous_coe_real.tendsto (0:ℚ)
  exact (he.comp (ScaledContactWeights318.weight_limit c hc)).prodMk
    ((he.comp (ScaledContactWeights318.weight7_limit c hc)).prodMk
      (he.comp (ScaledContactWeights318.weight25_limit c hc)))

lemma chain_actual (w : Assignment) (c t : ℚ) :
    ContactChainReal318.chain (project w,weights c t)=
      ((realChain w c t:ℝ),(imagChain w c t:ℝ)) := by
  simp only [ContactChainReal318.chain,weights,ContactChainReal318.value187_cast,
    ContactChainReal318.value188_cast,realChain,imagChain,ScaledDetectorChain318.view]

lemma inverse_scale_limit (c : ℚ) (hc : c≠0) :
    Tendsto (fun t => contact (parameter c t)/(c^10*(delta c t)^6)) atTop (𝓝 0) := by
  have ht := (ContactWeightLimits318.inverse_ed_limit.comp (parameter_limit c hc)).const_mul (c^10)⁻¹
  have he : (fun t => contact (parameter c t)/(c^10*(delta c t)^6))=
      fun t => (c^10)⁻¹*(contact (parameter c t)/(parameter c t-1)^6) := by
    funext t
    dsimp [delta]
    simp only [div_mul_eq_div_div,div_eq_mul_inv]
    ring
  rw [he]
  simpa only [Function.comp_def,mul_zero] using ht

/-- Uniformity is over the exact146 stored coefficients, not over independent
replacement detector values. The tube is chosen before the rational t and
before any later assignment lying in K. -/
theorem uniform_chain_box (c : ℚ) (hc : c≠0) (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, ∀ w : Assignment, project w∈K →
      3/4<realChain w c t ∧ realChain w c t<5/4 ∧
        -(1/4)<imagChain w c t ∧ imagChain w c t<1/4 := by
  let S : Set (Coeff × (ℝ × ℝ × ℝ)) :=
    {p | 3/4<(chain p).1 ∧ (chain p).1<5/4 ∧
      -(1/4)<(chain p).2 ∧ (chain p).2<1/4}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const chain_continuous.fst).inter
      ((isOpen_lt chain_continuous.fst continuous_const).inter
        ((isOpen_lt continuous_const chain_continuous.snd).inter
          (isOpen_lt chain_continuous.snd continuous_const)))
  have hKS : K ×ˢ ({(0,0,0)} : Set (ℝ × ℝ × ℝ)) ⊆ S := by
    rintro ⟨w,v⟩ ⟨hw,hv⟩
    have hv' : v=(0,0,0) := mem_singleton_iff.mp hv
    subst v
    change 3/4<(chain (w,(0,0,0))).1 ∧ _
    rw [chain_zero]
    norm_num
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hS hKS
  have hz : (0,0,0)∈V := h0V (by simp)
  filter_upwards [(weights_limit c hc).eventually (hV.mem_nhds hz)] with t ht
  intro w hw
  have hb := hUV ⟨hKU hw,ht⟩
  change 3/4<(chain (project w,weights c t)).1 ∧ _ at hb
  rw [show chain (project w,weights c t)=
    ((realChain w c t:ℝ),(imagChain w c t:ℝ)) from chain_actual w c t] at hb
  exact_mod_cast hb

/-- A single threshold works for all actual assignments in a compact
coefficient set. This fixes the order of the analytic choices without
silently asserting that a later arithmetic orbit belongs to that set. -/
theorem uniform_pole_domain (c : ℚ) (hc : c≠0) (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, 2<parameter c t ∧ ∀ w : Assignment, project w∈K →
      realChain w c t≠0 ∧ 0<poleInput w c t ∧ poleInput w c t<17 := by
  have hi := (inverse_scale_limit c hc).eventually
    (Iio_mem_nhds (by norm_num : (0:ℚ)<1))
  have hr := (parameter_limit c hc).eventually (eventually_gt_atTop (2:ℚ))
  filter_upwards [uniform_chain_box c hc K hK,hr,hi] with t hbox ht hi
  refine ⟨ht,?_⟩
  intro w hw
  obtain ⟨ha,ha',hb,hb'⟩ := hbox w hw
  have hn : realChain w c t≠0 := by linarith
  have hq := UniformPoleDomain318.quotient_box (realChain w c t) (imagChain w c t) ha ha' hb hb'
  change 0<traceQuotient w c t ∧ traceQuotient w c t<2 at hq
  have hf := ContactChainLimits318.contact_positive (parameter c t) ht
  have hd : 0<delta c t := by unfold delta; linarith
  have hc10 : 0<c^10 := by
    have hp := pow_pos (sq_pos_of_ne_zero hc) 5
    simpa only [←pow_mul] using hp
  have hv : 0<contact (parameter c t)/(c^10*(delta c t)^6) :=
    div_pos hf (mul_pos hc10 (pow_pos hd _))
  have hq2 : (traceQuotient w c t)^2<4 := by nlinarith [hq.1,hq.2]
  have hp : poleInput w c t<4 := by
    unfold poleInput
    rw [mul_div_assoc]
    calc
      (traceQuotient w c t)^2*(contact (parameter c t)/(c^10*(delta c t)^6)) < 4*1 :=
        mul_lt_mul hq2 (le_of_lt hi) hv (by norm_num)
      _ = 4 := by norm_num
  refine ⟨hn,?_,by linarith⟩
  unfold poleInput
  rw [mul_div_assoc]
  exact mul_pos (sq_pos_of_pos hq.1) hv

end UniformScaledPoleDomain318
