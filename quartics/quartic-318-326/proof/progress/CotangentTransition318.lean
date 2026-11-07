module
public import FrameTransition318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 HolomorphicCharts318
open Filter Topology
namespace CotangentTransition318
set_option maxHeartbeats 0

/-- The derivative of an actual inverse-sheet coordinate change is that of the
actual locally constant deck transformation, not an assumed automorphy factor. -/
theorem inverse_derivative_deck (N:ℕ) (hN:5≤N)
    (e:OpenPartialHomeomorph (Base (image N)) UpperHalfPlane)
    (he:(e.symm:UpperHalfPlane→Base (image N))=quotientMap N)
    (z:UpperHalfPlane) (hz:quotientMap N z∈e.source) :
    ∃g:image N,g•z=e (quotientMap N z) ∧
      deriv (fun w:ℂ=>(e (quotientMap N (ofComplex w)):ℂ)) (z:ℂ)=derivative g z := by
  have hf:ContinuousAt ofComplex (z:ℂ):=(contMDiffAt_ofComplex (n:=0) z.im_pos).continuousAt
  have hp:ContinuousAt (fun w:ℂ=>quotientMap N (ofComplex w)) (z:ℂ) :=
    (quotient_covering N hN).isCoveringMap.continuous.continuousAt.comp hf
  have hz':quotientMap N (ofComplex (z:ℂ))∈e.source := by simpa using hz
  have hg:ContinuousAt (fun w:ℂ=>e (quotientMap N (ofComplex w))) (z:ℂ) :=
    (e.continuousAt hz').comp (f:=fun w:ℂ=>quotientMap N (ofComplex w)) hp
  have hev:∀ᶠw in 𝓝 (z:ℂ),quotientMap N (ofComplex w)∈e.source :=
    hp.eventually (e.open_source.mem_nhds hz')
  have hsame:∀ᶠw in 𝓝 (z:ℂ),quotientMap N (ofComplex w)=
      quotientMap N (e (quotientMap N (ofComplex w))) := by
    filter_upwards [hev] with w hw
    have hh:=e.left_inv hw
    rw [he] at hh
    exact hh.symm
  obtain ⟨g,hg⟩:=LocalDeck318.locally_deck_eq N hN ofComplex
    (fun w:ℂ=>e (quotientMap N (ofComplex w))) (z:ℂ) hf hg hsame
  have heq:(fun w:ℂ=>(g•ofComplex w:UpperHalfPlane):ℂ→ℂ)=ᶠ[𝓝 (z:ℂ)]
      (fun w:ℂ=>(e (quotientMap N (ofComplex w)):ℂ)) := by
    filter_upwards [hg] with w hw
    exact congrArg UpperHalfPlane.coe hw
  refine ⟨g,by simpa only [ofComplex_apply] using hg.self_of_nhds,?_⟩
  rw [←heq.deriv_eq]
  exact (derivative_eq g z).symm

/-- The actual local trivialization cocycle is precisely the cotangent-square
coordinate cocycle: divide by the square of the actual chart-transition derivative. -/
theorem cotangent_square_transition (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane)
    (b:Base (image N)) (ha:b∈sheet N hN a) (hc:b∈sheet N hN c) (q:ℂ) :
    trivialization N hN c (frameMap N hN a (⟨b,ha⟩,q))=
      (b,q/(deriv ((localChart N hN a).symm.trans (localChart N hN c))
        (lift N hN a ⟨b,ha⟩:ℂ))^2) := by
  let z:UpperHalfPlane:=lift N hN a ⟨b,ha⟩
  have hz:quotientMap N z=b := lift_projection N hN a ⟨b,ha⟩
  have hzc:quotientMap N z∈((quotient_localHomeomorph N hN).localInverseAt c).source := by
    rw [hz];exact hc
  obtain ⟨g,hg,hd⟩:=inverse_derivative_deck N hN _
    ((quotient_localHomeomorph N hN).localInverseAt_symm c) z hzc
  have hg':g•lift N hN a ⟨b,ha⟩=lift N hN c ⟨b,hc⟩ := by
    change g•z=((quotient_localHomeomorph N hN).localInverseAt c) b
    rw [hz] at hg
    exact hg
  rw [trivialization_transition N hN a c b ha hc g hg' q]
  congr 2
  have he:(((localChart N hN a).symm.trans (localChart N hN c)):ℂ→ℂ)=
      (fun w:ℂ=>((quotient_localHomeomorph N hN).localInverseAt c (quotientMap N (ofComplex w)):ℂ)) := by
    ext w
    simp only [OpenPartialHomeomorph.coe_trans,Function.comp_apply,localChart_apply,localChart_symm_apply]
  rw [he]
  exact congrArg (fun x:ℂ=>x^2) hd.symm
/-- The actual complex transition derivative is nonzero everywhere on its source. -/
theorem transition_derivative_ne_zero (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane)
    (w:ℂ) (hw:w∈((localChart N hN a).symm.trans (localChart N hN c)).source) :
    deriv ((localChart N hN a).symm.trans (localChart N hN c)) w≠0 := by
  have hpos:=localChart_target_positive N hN a w hw.1
  let z:UpperHalfPlane:=⟨w,hpos⟩
  have hc:quotientMap N z∈((quotient_localHomeomorph N hN).localInverseAt c).source := by
    have hh:(localChart N hN a).symm w∈(localChart N hN c).source:=hw.2
    have hh':(localChart N hN a).symm w∈((quotient_localHomeomorph N hN).localInverseAt c).source:=hh.1
    simpa only [localChart_symm_apply,ofComplex_apply_of_im_pos hpos] using hh'
  obtain ⟨g,_,hd⟩:=inverse_derivative_deck N hN _
    ((quotient_localHomeomorph N hN).localInverseAt_symm c) z hc
  have he:(((localChart N hN a).symm.trans (localChart N hN c)):ℂ→ℂ)=
      (fun v:ℂ=>((quotient_localHomeomorph N hN).localInverseAt c (quotientMap N (ofComplex v)):ℂ)) := by
    ext v
    simp only [OpenPartialHomeomorph.coe_trans,Function.comp_apply,localChart_apply,localChart_symm_apply]
  rw [he]
  change deriv _ (z:ℂ)≠0
  rw [hd]
  exact derivative_ne_zero g z

/-- The actual inverse derivative-square line transition factor is holomorphic. -/
theorem analytic_cotangent_factor (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun w:ℂ=>
      ((deriv ((localChart N hN a).symm.trans (localChart N hN c)) w)⁻¹)^2)
      ((localChart N hN a).symm.trans (localChart N hN c)).source := by
  intro w hw
  exact (((analytic_transition N hN a c w hw).deriv).inv
    (transition_derivative_ne_zero N hN a c w hw)).pow 2
end CotangentTransition318
