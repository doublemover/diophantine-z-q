module
public import BoundedVertexExtension318
public import LegendreActualInfinityBranch318
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace LegendrePuncturedInfinityExtension318
open Set Filter
open scoped Topology
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreProjectiveModel318
@[expose] def unitPolynomial (l w:ℂ):ℂ:=(1-w^2)*(1-l*w^2)
@[expose] def nativeU (l:ℂ) (Y:ℂ→ℂ) (w:ℂ):ℂ:=w*(1-shift l*w^2)/Y w
@[expose] def nativeV (Y:ℂ→ℂ) (w:ℂ):ℂ:=w^3/Y w
lemma scaled_equation (l w y:ℂ) (hw:w≠0) (hy:y^2=polynomial l ((w^2)⁻¹)) :
    (w^3*y)^2=unitPolynomial l w := by
  rw [mul_pow,hy]
  dsimp [polynomial,unitPolynomial]
  field_simp [hw]
  <;> ring
lemma native_equation (l w Y:ℂ) (hY:Y≠0) (hs:Y^2=unitPolynomial l w) :
    LegendreInfinityBranchGerm318.equation l (w*(1-shift l*w^2)/Y) (w^3/Y)=0 := by
  have he:LegendreInfinityBranchGerm318.equation l (w*(1-shift l*w^2)/Y) (w^3/Y)=
      (w^3/Y^3)*(Y^2-unitPolynomial l w):=by
    dsimp [LegendreInfinityBranchGerm318.equation,unitPolynomial,A,B,shift]
    field_simp [hY]
    <;> ring
  rw [he,hs,sub_self,mul_zero]

/-- In the SAME original reciprocal source parameter t=w⁻², the scaled
y coordinate has a removable UNIT extension. The native target infinity
coordinates are constructed from it; no target chart containment or
continuity at infinity is assumed. -/
theorem extend (l:ℂ) (y:ℂ→ℂ)
    (hy:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ y w)
    (he:∀ᶠ w in 𝓝[≠] (0:ℂ),y w^2=polynomial l ((w^2)⁻¹)) :
    ∃Y:ℂ→ℂ,AnalyticAt ℂ Y 0 ∧ Y 0^2=1 ∧
      Y=ᶠ[𝓝[≠] (0:ℂ)] (fun w=>w^3*y w) ∧
      (∀ᶠ w in 𝓝 (0:ℂ),Y w≠0 ∧ Y w^2=unitPolynomial l w) ∧
      AnalyticAt ℂ (nativeU l Y) 0 ∧ AnalyticAt ℂ (nativeV Y) 0 ∧
      nativeU l Y 0=0 ∧ nativeV Y 0=0 ∧ deriv (nativeU l Y) 0≠0 ∧
      (∀ᶠ w in 𝓝 (0:ℂ),LegendreInfinityBranchGerm318.equation l
        (nativeU l Y w) (nativeV Y w)=0) ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ),
        nativeU l Y w=(((w^2)⁻¹-shift l)/y w) ∧ nativeV Y w=(y w)⁻¹) := by
  let f:ℂ→ℂ:=fun w=>w^3*y w
  have hfd:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ f w:=by
    filter_upwards [hy] with w hw
    exact ((differentiableAt_id.pow 3).mul hw)
  have hfs:∀ᶠ w in 𝓝[≠] (0:ℂ),f w^2=unitPolynomial l w:=by
    filter_upwards [he,self_mem_nhdsWithin] with w hw hne
    exact scaled_equation l w (y w) hne hw
  have hpoly:ContinuousAt (unitPolynomial l) 0:=by dsimp [unitPolynomial];fun_prop
  have hb:∀ᶠ w in 𝓝 (0:ℂ),‖unitPolynomial l w‖<4:=
    hpoly.norm.eventually (gt_mem_nhds (by norm_num [unitPolynomial]))
  have hbound:∀ᶠ w in 𝓝[≠] (0:ℂ),‖f w‖≤2:=by
    filter_upwards [hfs,hb.filter_mono nhdsWithin_le_nhds] with w hw hb'
    have hn:‖f w‖^2=‖unitPolynomial l w‖:=by simpa only [norm_pow] using congrArg norm hw
    nlinarith [norm_nonneg (f w)]
  obtain ⟨Y,hY,hYf,hlim⟩:=BoundedVertexExtension318.analytic_extension hfd 2 hbound
  have hY0:Y 0^2=(1:ℂ):=by
    have hp:Tendsto (unitPolynomial l) (𝓝[≠] (0:ℂ)) (𝓝 (1:ℂ)):=by
      simpa only [unitPolynomial,zero_pow (by decide:2≠0),sub_zero,mul_zero,mul_one] using
        hpoly.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hlim.pow 2) (hp.congr' hfs.symm)
  have hYn:Y 0≠0:=by intro h;rw [h,zero_pow (by decide:2≠0)] at hY0;exact zero_ne_one hY0
  have hYsq:∀ᶠ w in 𝓝 (0:ℂ),Y w^2=unitPolynomial l w:=by
    have he':∀ᶠ w in 𝓝[≠] (0:ℂ),Y w^2=unitPolynomial l w:=by
      filter_upwards [hYf,hfs] with w hf hs
      rw [hf,hs]
    have hh:=eventually_nhdsWithin_iff.mp he'
    filter_upwards [hh] with w hw
    by_cases hz:w=0
    · simpa [hz,unitPolynomial] using hY0
    · exact hw hz
  have hunit:∀ᶠ w in 𝓝 (0:ℂ),Y w≠0:=hY.continuousAt.eventually_ne hYn
  have hU:AnalyticAt ℂ (nativeU l Y) 0:=by
    unfold nativeU
    exact (analyticAt_id.mul (analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2)))).div hY hYn
  have hV:AnalyticAt ℂ (nativeV Y) 0:=(analyticAt_id.pow 3).div hY hYn
  have hU0:nativeU l Y 0=0:=by simp [nativeU]
  have hV0:nativeV Y 0=0:=by simp [nativeV]
  have hUd:HasDerivAt (nativeU l Y) (1/Y 0) 0:=by
    have ha:HasDerivAt (fun w:ℂ=>w*(1-shift l*w^2)) 1 0:=by
      convert (hasDerivAt_id (0:ℂ)).mul
        ((hasDerivAt_const (0:ℂ) (1:ℂ)).sub (((hasDerivAt_id (0:ℂ)).pow 2).const_mul (shift l))) using 1 <;> simp
    convert ha.div hY.differentiableAt.hasDerivAt hYn using 1 <;>
      simp [nativeU] <;> field_simp [hYn] <;> ring
  have hUdne:deriv (nativeU l Y) 0≠0:=by rw [hUd.deriv];exact div_ne_zero one_ne_zero hYn
  refine ⟨Y,hY,hY0,hYf,hunit.and hYsq,hU,hV,hU0,hV0,hUdne,?_,?_⟩
  · filter_upwards [hunit,hYsq] with w hw hs
    exact native_equation l w (Y w) hw hs
  · filter_upwards [hYf,hunit.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hunit' hne
    have hyn:y w≠0:=by
      intro h
      apply hunit'
      rw [hw]
      simp only [h,mul_zero]
    change w*(1-shift l*w^2)/Y w= _ ∧ w^3/Y w= _
    rw [hw]
    constructor <;> field_simp [hne,hyn] <;> ring
end LegendrePuncturedInfinityExtension318
