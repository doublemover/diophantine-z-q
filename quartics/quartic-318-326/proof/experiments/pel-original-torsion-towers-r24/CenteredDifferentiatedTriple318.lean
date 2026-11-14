module
public import LocalAdditiveGerm318
public import EntireSimultaneousNonzero318
public section
noncomputable section
namespace CenteredDifferentiatedTriple318
open Set Filter Metric Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
/-- A differentiated mixed triple identity forces an affine logarithmic
variation. Ratios occur only on a produced nonzero ball; the final
cross-multiplied identity is entire and includes every zero. -/
theorem affine_ratio(F A H B:E→ℂ)(c:ℂ)
    (hF:Differentiable ℂ F)(hA:Differentiable ℂ A)(hH:ContinuousAt H 0)
    (hF0:F 0≠0)(hH0:H 0≠0)
    (ht:∀a b:E,A a*F b*H (-a-b)+F a*A b*H (-a-b)+F a*F b*B (-a-b)=
      c*(F a*F b*H (-a-b))):
    ∃l:E→ₗ[ℂ]ℂ,∀v:E,A v=(A 0/F 0+l v)*F v:=by
  let R:E→ℂ:=fun a=>A a/F a
  have hn:∀ᶠa in 𝓝 (0:E),F a≠0∧H (-a)≠0:=by
    have hf:∀ᶠa in 𝓝 (0:E),F a≠0:=hF.continuous.continuousAt.eventually_ne hF0
    have hh:∀ᶠa in 𝓝 (0:E),H (-a)≠0:=
      (hH.comp 0 continuousAt_neg).eventually_ne (by simpa only [neg_zero] using hH0)
    exact hf.and hh
  obtain ⟨r,hr,hnr⟩:=Metric.eventually_nhds_iff.mp hn
  have hnr':∀a:E,‖a‖<r→F a≠0∧H (-a)≠0:=by
    intro a ha
    exact hnr (by simpa only [dist_zero_right] using ha)
  have hR:∀a:E,‖a‖<r→DifferentiableAt ℂ R a:=by
    intro a ha
    exact (hA a).div (hF a) (hnr' a ha).1
  have hadd:∀a b:E,‖a‖<r→‖b‖<r→‖a+b‖<r→R (a+b)+R 0=R a+R b:=by
    intro a b ha hb hab
    have h1:=ht a b
    have h2:=ht (a+b) 0
    have hs:-a-b=-(a+b):=by abel
    rw [hs] at h1
    simp only [sub_zero] at h2
    have hp:(A (a+b)*F 0+F (a+b)*A 0)*(F a*F b)=
        (A a*F b+F a*A b)*(F (a+b)*F 0):=by
      apply mul_left_cancel₀ (hnr' (a+b) hab).2
      linear_combination (F a*F b)*h2-(F (a+b)*F 0)*h1
    dsimp only [R]
    field_simp [(hnr' a ha).1,(hnr' b hb).1,(hnr' (a+b) hab).1,hF0]
    linear_combination hp
  have hd0:DifferentiableAt ℂ R 0:=hR 0 (by simpa using hr)
  let l:E→ₗ[ℂ]ℂ:=(fderiv ℂ R 0).toLinearMap
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
  let Rv:ℂ→ℂ:=fun t=>R (t • v)
  have hmap:Differentiable ℂ (fun t:ℂ=>t • v):=differentiable_id.smul_const v
  have hdv:HasDerivAt Rv (l v) 0:=by
    simpa only [Rv,l,zero_smul,one_smul] using
      hd0.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℂ)).smul_const v)
  have hg:=LocalAdditiveGerm318.affine_germ Rv rv hrv
    (fun t ht=>(hR (t • v) (hline t ht)).comp t (hmap t)) (by
      intro a b ha hb hab
      simpa only [Rv,zero_smul,add_smul] using
        hadd (a • v) (b • v) (hline a ha) (hline b hb)
          (by simpa only [add_smul] using hline (a+b) hab))
  rw [hdv.deriv] at hg
  let D:ℂ→ℂ:=fun t=>A (t • v)-(A 0/F 0+l v*t)*F (t • v)
  have hD:Differentiable ℂ D:=
    (hA.comp hmap).sub ((differentiable_const.add
      (differentiable_const.mul differentiable_id)).mul (hF.comp hmap))
  have hz:D=ᶠ[𝓝 (0:ℂ)] 0:=by
    have hfn:∀ᶠt in 𝓝 (0:ℂ),F (t • v)≠0:=
      (hF.comp hmap).continuous.continuousAt.eventually_ne (by simpa only [zero_smul] using hF0)
    filter_upwards [hg,hfn] with t ht hft
    have he:A (t • v)=(A 0/F 0+l v*t)*F (t • v):=by
      change A (t • v)/F (t • v)=A 0/F 0+l v*t at ht
      exact (div_eq_iff hft).mp ht
    exact sub_eq_zero.mpr he
  have hglobal:EqOn D 0 Set.univ:=
    hD.differentiableOn.analyticOnNhd isOpen_univ |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ 0) hz
  have hfinal:=hglobal (Set.mem_univ (1:ℂ))
  simpa only [D,one_smul,mul_one,sub_eq_zero] using hfinal
end CenteredDifferentiatedTriple318
