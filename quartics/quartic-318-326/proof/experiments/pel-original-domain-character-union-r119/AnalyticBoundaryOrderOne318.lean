module
public import AnalyticHalfPlaneLeading318
public section
noncomputable section
namespace AnalyticBoundaryOrderOne318
open Complex Set Filter AnalyticHalfPlaneLeading318 UpperHalfPlanePowerRays318
open scoped Topology
set_option maxHeartbeats 2600000

/-- A genuine analytic boundary extension taking the real boundary to
itself and the upper half-neighborhood strictly into the upper half-plane
has order ONE at its zero. Interior injectivity alone is not used as a
substitute for this boundary argument. -/
theorem order_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (hr : ∀ᶠ z in 𝓝 (0:ℂ),z.im=0 → (f z).im=0)
    (hu : ∀ᶠ z in 𝓝 (0:ℂ),0<z.im → 0<(f z).im) :
    analyticOrderNatAt f 0=1 ∧ deriv f 0≠0 := by
  have htop : analyticOrderAt f 0≠⊤ := by
    intro hh
    have he := analyticOrderAt_eq_top.mp hh
    have hfalse : ∀ᶠ t in 𝓝[>] (0:ℝ),False := by
      filter_upwards [(ray_tendsto I).eventually he,(ray_tendsto I).eventually hu,
        self_mem_nhdsWithin] with t ht ht' htp
      have hi : 0<((t:ℂ)*I).im := by simpa using htp
      have hp := ht' hi
      rw [ht,Complex.zero_im] at hp
      exact lt_irrefl 0 hp
    obtain ⟨t,ht⟩ := hfalse.exists
    exact ht
  obtain ⟨g,hg,hg0,he⟩ := hf.analyticOrderAt_ne_top.mp htop
  let n := analyticOrderNatAt f 0
  have hfactor : ∀ᶠ z in 𝓝 (0:ℂ),f z=z^n*g z := by
    simpa only [sub_zero,smul_eq_mul] using he
  have hn0 : n≠0 := by
    intro hn
    have hh := hfactor.self_of_nhds
    rw [hf0,hn,pow_zero,one_mul] at hh
    exact hg0 hh.symm
  have hgReal := leading_real f g n hg.continuousAt hfactor hr
  have hnlt : n<2 := by
    by_contra hh
    obtain ⟨a,b,ha,hb,hap,hbp⟩ := opposite_power_rays n (by omega)
    have hp := upper_ray_leading f g n a hg.continuousAt ha hfactor hu
    have hm := upper_ray_leading f g n b hg.continuousAt hb hfactor hu
    rw [hap] at hp
    rw [hbp] at hm
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.neg_re,
      Complex.neg_im,zero_mul,one_mul,neg_zero,neg_one_mul,zero_add] at hp hm
    have hgre : (g 0).re=0 := by linarith
    exact hg0 (Complex.ext hgre hgReal)
  have hn : n=1 := by omega
  have hfac1 : f =ᶠ[𝓝 (0:ℂ)] (fun z => z*g z) := by
    simpa only [hn,pow_one] using hfactor
  have hder : HasDerivAt (fun z : ℂ => z*g z) (g 0) 0 := by
    convert (hasDerivAt_id (0:ℂ)).mul hg.differentiableAt.hasDerivAt using 1 <;> simp
  have hd : deriv f 0=g 0 := (hder.congr_of_eventuallyEq hfac1).deriv
  exact ⟨hn,by rw [hd]; exact hg0⟩
end AnalyticBoundaryOrderOne318
