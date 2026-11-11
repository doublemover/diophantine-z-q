module
public import LocalMultiplicativeGerm318
public import EntireSimultaneousNonzero318
public section
noncomputable section
namespace CenteredTripleProductRigidity318
open Set Filter Metric Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]

/-- A balanced triple identity is rigid even when the entire factors
have zeros. Only a small genuinely nonzero neighborhood is used for
ratios; the final identity extends by actual entire one-variable lines. -/
theorem exponential_ratio(F G H K:E→ℂ)(C:ℂ)
    (hF:Differentiable ℂ F)(hG:Differentiable ℂ G)(hH:ContinuousAt H 0)
    (hF0:F 0≠0)(hG0:G 0≠0)(hH0:H 0≠0)
    (htriple:∀a b:E,F a*F b*H (-a-b)=C*(G a*G b*K (-a-b))):
    ∃l:E→ₗ[ℂ]ℂ,∀v:E,F v=(F 0/G 0)*Complex.exp (l v)*G v:=by
  let R:E→ℂ:=fun a=>F a/G a
  have hn:∀ᶠa in 𝓝 (0:E),G a≠0∧H (-a)≠0:=by
    have hg:∀ᶠa in 𝓝 (0:E),G a≠0:=(hG.continuous.continuousAt).eventually_ne hG0
    have hh:∀ᶠa in 𝓝 (0:E),H (-a)≠0:=
      (hH.comp 0 continuousAt_neg).eventually_ne (by simpa only [neg_zero] using hH0)
    exact hg.and hh
  obtain ⟨r,hr,hnr⟩:=Metric.eventually_nhds_iff.mp hn
  have hnr':∀a:E,‖a‖<r→G a≠0∧H (-a)≠0:=by
    intro a ha
    exact hnr (by simpa only [dist_zero_right] using ha)
  have hR:∀a:E,‖a‖<r→DifferentiableAt ℂ R a:=by
    intro a ha
    exact (hF a).div (hG a) (hnr' a ha).1
  have hR0:R 0≠0:=div_ne_zero hF0 hG0
  have hm:∀a b:E,‖a‖<r→‖b‖<r→‖a+b‖<r→R (a+b)*R 0=R a*R b:=by
    intro a b ha hb hab
    have h1:=htriple a b
    have h2:=htriple (a+b) 0
    have hs:-a-b=-(a+b):=by abel
    rw [hs] at h1
    simp only [sub_zero] at h2
    have hp:F (a+b)*F 0*(G a*G b)=F a*F b*(G (a+b)*G 0):=by
      apply mul_left_cancel₀ (hnr' (a+b) hab).2
      calc
        H (-(a+b))*(F (a+b)*F 0*(G a*G b))=
          (F (a+b)*F 0*H (-(a+b)))*(G a*G b):=by ring
        _=C*(G (a+b)*G 0*K (-(a+b)))*(G a*G b):=by rw [h2]
        _=(C*(G a*G b*K (-(a+b))))*(G (a+b)*G 0):=by ring
        _=(F a*F b*H (-(a+b)))*(G (a+b)*G 0):=by rw [←h1]
        _=H (-(a+b))*(F a*F b*(G (a+b)*G 0)):=by ring
    dsimp only [R]
    field_simp [(hnr' a ha).1,(hnr' b hb).1,(hnr' (a+b) hab).1,hG0]
    linear_combination hp
  have hd0:DifferentiableAt ℂ R 0:=hR 0 (by simpa using hr)
  let l:E→ₗ[ℂ]ℂ:=(R 0)⁻¹ • (fderiv ℂ R 0).toLinearMap
  refine ⟨l,?_⟩
  intro v
  let rv:ℝ:=r/(‖v‖+1)
  have hvp:0<‖v‖+1:=by positivity
  have hrv:0<rv:=div_pos hr hvp
  have hline:∀t:ℂ,‖t‖<rv→‖t • v‖<r:=by
    intro t ht
    rw [norm_smul]
    calc
      ‖t‖*‖v‖≤‖t‖*(‖v‖+1):=mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg t)
      _<rv*(‖v‖+1):=mul_lt_mul_of_pos_right ht hvp
      _=r:=div_mul_cancel₀ r (ne_of_gt hvp)
  let f:ℂ→ℂ:=fun t=>F (t • v)
  let g:ℂ→ℂ:=fun t=>G (t • v)
  let Rv:ℂ→ℂ:=fun t=>R (t • v)
  have hmap:Differentiable ℂ (fun t:ℂ=>t • v):=differentiable_id.smul_const v
  have hf:Differentiable ℂ f:=hF.comp hmap
  have hg:Differentiable ℂ g:=hG.comp hmap
  have hdv:HasDerivAt Rv ((fderiv ℂ R 0) v) 0:=by
    simpa only [Rv,zero_smul,one_smul] using
      hd0.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℂ)).smul_const v)
  have hlocal:=LocalMultiplicativeGerm318.exponential_germ Rv rv hrv
    (by simpa only [Rv,zero_smul] using hR0)
    (fun t ht=>(hR (t • v) (hline t ht)).comp t (hmap t)) (by
      intro a b ha hb hab
      simpa only [Rv,zero_smul,add_smul] using
        hm (a • v) (b • v) (hline a ha) (hline b hb) (by simpa only [add_smul] using hline (a+b) hab))
  have hslope:deriv Rv 0/Rv 0=l v:=by
    rw [hdv.deriv]
    simp only [Rv,zero_smul,l,LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [hslope] at hlocal
  let D:ℂ→ℂ:=fun t=>f t-(F 0/G 0)*Complex.exp (l v*t)*g t
  have hD:Differentiable ℂ D:=
    hf.sub ((differentiable_const.mul (Complex.differentiable_exp.comp
      (differentiable_const.mul differentiable_id))).mul hg)
  have hzero:D=ᶠ[𝓝 (0:ℂ)] 0:=by
    have hgn:∀ᶠt in 𝓝 (0:ℂ),g t≠0:=
      hg.continuous.continuousAt.eventually_ne (by simpa only [g,zero_smul] using hG0)
    filter_upwards [hlocal,hgn] with t ht hgt
    have he:f t=(F 0/G 0)*Complex.exp (l v*t)*g t:=by
      change f t/g t=(F 0/G 0)*Complex.exp (l v*t) at ht
      exact (div_eq_iff hgt).mp ht
    exact sub_eq_zero.mpr he
  have hglobal:EqOn D 0 Set.univ:=
    hD.differentiableOn.analyticOnNhd isOpen_univ |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hzero
  have hfinal:=hglobal (Set.mem_univ (1:ℂ))
  simpa only [D,f,g,one_smul,mul_one,sub_eq_zero] using hfinal
end CenteredTripleProductRigidity318
