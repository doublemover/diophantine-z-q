module
public import ContactChainReal318
public section
noncomputable section
namespace UniformPoleDomain318
open Filter Set CircuitReplay ContactChainReal318 ContactWeightWitness318 PoleInputWitness318
open scoped Topology

@[expose] def weights (t : ℚ) : ℝ × ℝ × ℝ :=
  ((weight t:ℝ),(((weight t)^7*(t-1)^18:ℚ):ℝ),
    (((weight t)^25*(t-1)^72:ℚ):ℝ))

lemma weights_limit : Tendsto weights atTop (𝓝 (0,0,0)) := by
  have hc := Rat.continuous_coe_real.tendsto (0:ℚ)
  exact (hc.comp ContactWeightLimits318.weight_limit).prodMk
    ((hc.comp ContactWeightLimits318.weight7_limit).prodMk
      (hc.comp ContactWeightLimits318.weight25_limit))

/-- Uniformity is over the exact146 stored coefficients, not over independent
replacement detector values. The tube is chosen before the rational t and
before any later assignment lying in K. -/
theorem uniform_chain_box (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, ∀ w : Assignment, project w∈K →
      3/4<realChain w t ∧ realChain w t<5/4 ∧
        -(1/4)<imagChain w t ∧ imagChain w t<1/4 := by
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
  filter_upwards [weights_limit.eventually (hV.mem_nhds hz)] with t ht
  intro w hw
  have hb := hUV ⟨hKU hw,ht⟩
  change 3/4<(chain (project w,weights t)).1 ∧ _ at hb
  rw [show chain (project w,weights t)=
    ((realChain w t:ℝ),(imagChain w t:ℝ)) from chain_actual w t] at hb
  exact_mod_cast hb

lemma quotient_box (a b : ℚ)
    (ha : 3/4<a) (ha' : a<5/4) (hb : -(1/4)<b) (hb' : b<1/4) :
    0<(a^2-2*b^2)/(2*a) ∧ (a^2-2*b^2)/(2*a)<2 := by
  have hapos : 0<a := by linarith
  have hb2 : b^2<1/16 := by nlinarith [mul_pos (by linarith : 0<1/4-b)
    (by linarith : 0<1/4+b)]
  constructor
  · apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (a-3/4)]
  · apply (div_lt_iff₀ (by positivity : 0<2*a)).mpr
    nlinarith [sq_nonneg b,mul_pos hapos (by linarith : 0<5/4-a)]

/-- A single threshold works for all actual assignments in a compact
coefficient set. This fixes the order of the analytic choices without
silently asserting that a later arithmetic orbit belongs to that set. -/
theorem uniform_pole_domain (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, 2<t ∧ ∀ w : Assignment, project w∈K →
      realChain w t≠0 ∧ 0<poleInput w t ∧ poleInput w t<17 := by
  have hi := ContactWeightLimits318.inverse_ed_limit.eventually
    (Iio_mem_nhds (by norm_num : (0:ℚ)<1))
  filter_upwards [uniform_chain_box K hK,eventually_gt_atTop (2:ℚ),hi]
    with t hbox ht hi
  refine ⟨ht,?_⟩
  intro w hw
  obtain ⟨ha,ha',hb,hb'⟩ := hbox w hw
  have hn : realChain w t≠0 := by linarith
  have hq := quotient_box (realChain w t) (imagChain w t) ha ha' hb hb'
  change 0<traceQuotient w t ∧ traceQuotient w t<2 at hq
  have hf := ContactChainLimits318.contact_positive t ht
  have hd : 0<t-1 := by linarith
  have hv : 0<contact t/(t-1)^6 := div_pos hf (pow_pos hd _)
  have hq2 : (traceQuotient w t)^2<4 := by nlinarith [hq.1,hq.2]
  have hp : poleInput w t<4 := by
    unfold poleInput
    rw [mul_div_assoc]
    calc
      (traceQuotient w t)^2*(contact t/(t-1)^6) < 4*1 :=
        mul_lt_mul hq2 (le_of_lt hi) hv (by norm_num)
      _ = 4 := by norm_num
  exact ⟨hn,(pole_positive_iff w t hn (by linarith)).mpr hf,by linarith⟩

end UniformPoleDomain318
