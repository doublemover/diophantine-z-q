module
public import RotatedPartialChart318
public import HolomorphicInverse318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 RotatedProjection318 RotatedHomeomorph318 RotatedPartialChart318 HolomorphicCharts318
open scoped MatrixGroups Manifold ContDiff
namespace RotatedBiholomorphic318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem integral_smul_holomorphic (g:SL(2,ℤ)) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun tau:UpperHalfPlane=>g•tau) := by
  have h:ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun tau:UpperHalfPlane=>(g:GL (Fin 2) ℝ)•tau):=
    UpperHalfPlane.contMDiff_smul (by simp)
  exact h.congr (fun tau=>(ModularGroup.sl_moeb g tau).symm)

/-- The inverse actual width-coordinate is holomorphic, using the genuine
nonzero exponential derivative and a local logarithm at the chosen lift. -/
theorem inverse_holomorphic (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (inverseFunction N hN g) (punctured (wReal N hN g) 2) := by
  letI:=complexChartedSpace N hN
  intro q hq
  obtain ⟨tau,htau⟩:=qMap_surjective (wReal N hN g) 2 (wReal_pos N hN g) (by norm_num) ⟨q,hq⟩
  have hparam:Periodic.qParam (wReal N hN g) tau=q:=congrArg Subtype.val htau
  rw [←hparam]
  apply ContMDiffAt.contMDiffWithinAt
  let r:=WidthLocalInverse318.inverse (wReal N hN g) (wReal_pos N hN g) (tau:ℂ)
  have hr:AnalyticAt ℂ r (Periodic.qParam (wReal N hN g) tau):=
    WidthLocalInverse318.inverse_analytic _ _ tau
  have hr0:r (Periodic.qParam (wReal N hN g) tau)=(tau:ℂ):=
    WidthLocalInverse318.inverse_value _ _ tau
  have hp:0<(r (Periodic.qParam (wReal N hN g) tau)).im:=by rw [hr0];exact tau.val.im_pos
  have hof:=(UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) hp).comp
    (Periodic.qParam (wReal N hN g) tau) hr.contDiffAt.contMDiffAt
  have hg:=(integral_smul_holomorphic g (ofComplex (r (Periodic.qParam (wReal N hN g) tau)))).comp
    (Periodic.qParam (wReal N hN g) tau) hof
  have hc:=(HolomorphicProjection318.quotient_holomorphic N hN
    (g•ofComplex (r (Periodic.qParam (wReal N hN g) tau)))).comp
    (Periodic.qParam (wReal N hN g) tau) hg
  apply hc.congr_of_eventuallyEq
  have hh:∀ᶠv in 𝓝 (Periodic.qParam (wReal N hN g) tau),(2:ℝ)<(r v).im:=by
    apply ((Complex.continuous_im.continuousAt).comp hr.continuousAt).eventually
    apply isOpen_Ioi.mem_nhds
    change (2:ℝ)<(r (Periodic.qParam (wReal N hN g) tau)).im
    rw [hr0]
    exact tau.property
  filter_upwards [hh,WidthLocalInverse318.inverse_right (wReal N hN g) (wReal_pos N hN g) (tau:ℂ)] with v hv hright
  have hpos:0<(r v).im:=lt_trans (by norm_num : (0:ℝ)<2) hv
  let t:UpperHalfPlane:=⟨r v,hpos⟩
  have ht:t∈high 2:=hv
  have hqt:Periodic.qParam (wReal N hN g) t=v:=hright
  calc
    inverseFunction N hN g v=inverseFunction N hN g (Periodic.qParam (wReal N hN g) t):=congrArg _ hqt.symm
    _ = quotientMap N (g•t):=inverseFunction_projection N hN g ⟨t,ht⟩
    _ = quotientMap N (g•ofComplex (r v)):=by
      congr 2
      exact (ofComplex_apply_of_im_pos hpos).symm

/-- The forward actual width-coordinate is holomorphic in the existing
quotient complex atlas, by the proved holomorphic local inverse sheets. -/
theorem coordinate_holomorphic (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (coordinateFunction N hN g) (neighborhood N g) := by
  letI:=complexChartedSpace N hN
  intro b hb
  obtain ⟨tau,htau,hb⟩:=hb
  subst b
  let a:UpperHalfPlane:=g•tau
  let e:OpenPartialHomeomorph (Base (image N)) UpperHalfPlane:=
    (quotient_localHomeomorph N hN).localInverseAt a
  have he:quotientMap N a∈e.source:=
    (quotient_localHomeomorph N hN).apply_self_mem_localInverseAt_source
  have hea:e (quotientMap N a)=a:=(quotient_localHomeomorph N hN).localInverseAt_apply_self
  have heh:ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e (quotientMap N a):=
    (HolomorphicInverse318.localInverseAt_holomorphic N hN a _ he).contMDiffAt (e.open_source.mem_nhds he)
  have hrot:=(integral_smul_holomorphic g⁻¹ (e (quotientMap N a))).comp (quotientMap N a) heh
  have hcoe:=UpperHalfPlane.contMDiff_coe.contMDiffAt.comp (quotientMap N a) hrot
  have hc:=(Periodic.contDiff_qParam (h:=wReal N hN g) ω).contMDiff.contMDiffAt.comp
    (quotientMap N a) hcoe
  apply ContMDiffAt.contMDiffWithinAt
  apply hc.congr_of_eventuallyEq
  have hhigh:∀ᶠu in 𝓝 (quotientMap N a),(2:ℝ)<(g⁻¹•e u).im:=by
    apply (continuous_im.continuousAt.comp hrot.continuousAt).eventually
    apply isOpen_Ioi.mem_nhds
    change (2:ℝ)<(g⁻¹•e (quotientMap N a)).im
    rw [hea]
    change (2:ℝ)<(g⁻¹•(g•tau)).im
    rw [inv_smul_smul]
    exact htau
  filter_upwards [hhigh,e.open_source.mem_nhds he] with u hu hus
  have heq:quotientMap N (e u)=u:=by
    have h:=e.left_inv hus
    change ((quotient_localHomeomorph N hN).localInverseAt a).symm (e u)=u at h
    rw [(quotient_localHomeomorph N hN).localInverseAt_symm] at h
    exact h
  have hparam:=coordinateFunction_projection N hN g ⟨g⁻¹•e u,hu⟩
  simpa only [smul_inv_smul,heq,Function.comp_apply] using hparam

/-- Both directions of every actual rotated cusp chart are holomorphic. -/
theorem chart_biholomorphic (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chart N hN g) (chart N hN g).source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chart N hN g).symm (chart N hN g).target := by
  letI:=complexChartedSpace N hN
  exact ⟨coordinate_holomorphic N hN g,inverse_holomorphic N hN g⟩

end RotatedBiholomorphic318
