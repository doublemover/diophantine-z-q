module
public import BoundedVanishingJumpGluing318
public section
noncomputable section
namespace ModulusSchwarzExtension318
open Set Metric Filter
open scoped Topology ComplexConjugate
open HolomorphicRectanglePrimitive318 ActualBoundedPrimitiveTraces318
set_option maxHeartbeats 2800000

@[expose] def reciprocalReflection (f:ℂ→ℂ) (z:ℂ) : ℂ := (conj (f (conj z)))⁻¹

theorem conjugate_lower_mem {a b r:ℝ} {z:ℂ}
    (hz:z∈openRectangle a b (-r) 0) : conj z∈openRectangle a b 0 r := by
  change (a<z.re ∧ z.re<b) ∧ (-r<z.im ∧ z.im<0) at hz
  change (a<(conj z).re ∧ (conj z).re<b) ∧ (0<(conj z).im ∧ (conj z).im<r)
  simpa only [Complex.conj_re,Complex.conj_im] using
    And.intro hz.1 (And.intro (neg_pos.mpr hz.2.2) (neg_lt.mp hz.2.1))

theorem conjugate_upper_mem {a b r:ℝ} {z:ℂ}
    (hz:z∈openRectangle a b 0 r) : conj z∈openRectangle a b (-r) 0 := by
  change (a<z.re ∧ z.re<b) ∧ (0<z.im ∧ z.im<r) at hz
  change (a<(conj z).re ∧ (conj z).re<b) ∧ (-r<(conj z).im ∧ (conj z).im<0)
  simpa only [Complex.conj_re,Complex.conj_im] using
    And.intro hz.1 (And.intro (neg_lt_neg hz.2.2) (neg_lt_zero.mpr hz.2.1))

/-- The lower function is derived by genuine conjugate-conjugate
holomorphy and inversion on the original nonzero collar. -/
theorem reciprocal_differentiable (f:ℂ→ℂ) {a b r:ℝ}
    (hf:DifferentiableOn ℂ f (openRectangle a b 0 r))
    (hlo:∀z∈openRectangle a b 0 r,(1/2:ℝ)≤‖f z‖) :
    DifferentiableOn ℂ (reciprocalReflection f) (openRectangle a b (-r) 0) := by
  intro z hz
  have hzc := conjugate_lower_mem hz
  have hd : DifferentiableAt ℂ f (conj z) :=
    (hf _ hzc).differentiableAt ((openRectangle_open a b 0 r).mem_nhds hzc)
  have hh : DifferentiableAt ℂ (conj ∘ f ∘ conj) z :=
    differentiableAt_conj_conj_iff.mpr hd
  have hn : conj (f (conj z))≠0 := by
    have hp : 0<‖f (conj z)‖ := lt_of_lt_of_le (by norm_num) (hlo _ hzc)
    have hf0 : f (conj z)≠0 := norm_pos_iff.mp hp
    simpa using hf0
  exact (hh.inv hn).differentiableWithinAt

theorem reciprocal_bound (f:ℂ→ℂ) {a b r:ℝ}
    (hlo:∀z∈openRectangle a b 0 r,(1/2:ℝ)≤‖f z‖)
    {z:ℂ} (hz:z∈openRectangle a b (-r) 0) : ‖reciprocalReflection f z‖≤2 := by
  have hh := hlo _ (conjugate_lower_mem hz)
  have hp : 0<‖f (conj z)‖ := lt_of_lt_of_le (by norm_num) hh
  simp only [reciprocalReflection,norm_inv,Complex.norm_conj]
  have hh2:1≤2*‖f (conj z)‖:=by linarith
  have hm:=mul_le_mul_of_nonneg_right hh2 (inv_nonneg.mpr hp.le)
  simpa only [one_mul,mul_assoc,mul_inv_cancel₀ (ne_of_gt hp),mul_one] using hm

/-- Schwarz extension from MODULUS boundary limits, not prescribed
complex boundary values. The bounded collar and actual inverse reflection
give the vanishing jump; the primitive/Morera construction supplies the
analytic extension across the whole original interval. -/
theorem extension_of_modulus (f:ℂ→ℂ) {a b r:ℝ} (hab:a<b) (hr:0<r)
    (hf:DifferentiableOn ℂ f (openRectangle a b 0 r))
    (hlo:∀z∈openRectangle a b 0 r,(1/2:ℝ)≤‖f z‖)
    (hhi:∀z∈openRectangle a b 0 r,‖f z‖≤1)
    (hmod:∀x∈Ioo a b,Tendsto (fun z=>‖f z‖)
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 1)) :
    ∃F:ℂ→ℂ,DifferentiableOn ℂ F (openRectangle a b (-r) r) ∧
      (∀z∈openRectangle a b 0 r,F z=f z) ∧
      (∀z∈openRectangle a b (-r) 0,F z=reciprocalReflection f z) := by
  apply BoundedVanishingJumpGluing318.bounded_vanishing_jump_gluing f
    (reciprocalReflection f) hab hr hf (reciprocal_differentiable f hf hlo) 1 2
  · intro z hz
    exact_mod_cast hhi z hz
  · intro z hz
    exact_mod_cast reciprocal_bound f hlo hz
  · intro x hx
    simpa [reciprocalReflection] using
      ConformalBoundaryModulus318.reflected_jump_tendsto_zero _ f (hmod x hx)
/-- Unit-circle boundary values are a CONSEQUENCE of the constructed
holomorphic extension and the original modulus limit, not an input to
Schwarz reflection. -/
theorem seam_norm_one (f F:ℂ→ℂ) {a b r:ℝ} (hr:0<r)
    (hF:DifferentiableOn ℂ F (openRectangle a b (-r) r))
    (hag:∀z∈openRectangle a b 0 r,F z=f z)
    (hmod:∀x∈Ioo a b,Tendsto (fun z=>‖f z‖)
      (𝓝[openRectangle a b 0 r] (x:ℂ)) (𝓝 1))
    {x:ℝ} (hx:x∈Ioo a b) : ‖F (x:ℂ)‖=1 := by
  have hxfull:(x:ℂ)∈openRectangle a b (-r) r := by
    change (x:ℂ).re∈Ioo a b ∧ (x:ℂ).im∈Ioo (-r) r
    simpa using And.intro hx (And.intro (neg_lt_zero.mpr hr) hr)
  have hc:ContinuousAt F (x:ℂ) :=
    ((hF _ hxfull).differentiableAt ((openRectangle_open a b (-r) r).mem_nhds hxfull)).continuousAt
  have ht : ∀ᶠt in 𝓝[>] (0:ℝ),upperPath x t∈openRectangle a b 0 r := by
    have htr : ∀ᶠt in 𝓝[>] (0:ℝ),t<r := nhdsWithin_le_nhds (eventually_lt_nhds hr)
    filter_upwards [self_mem_nhdsWithin,htr] with t hp hlt
    exact upper_path_mem hx hp hlt
  have hpath : Tendsto (upperPath x) (𝓝[>] (0:ℝ)) (𝓝[openRectangle a b 0 r] (x:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨upper_path_limit x,ht⟩
  have h₁ := (hc.tendsto.comp (upper_path_limit x)).norm
  have h₂ := (hmod x hx).comp hpath
  have he : (fun t=>‖F (upperPath x t)‖)=ᶠ[𝓝[>] (0:ℝ)] (fun t=>‖f (upperPath x t)‖) :=
    ht.mono (fun t ht=>congrArg norm (hag _ ht))
  exact tendsto_nhds_unique h₁ ((tendsto_congr' he).mpr h₂)
end ModulusSchwarzExtension318
