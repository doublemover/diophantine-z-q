module
public import PELOriginalFlatSymplecticTransport318
public import PELOriginalSecondFundamentalMetric318
public section
noncomputable section
namespace PELOriginalKernelMonodromyCovariance318
open Filter
open scoped Topology
open QuaternionicRealPeriod318 PELOriginalSiegelNormalization318
open PELOriginalFlatPeriodKernel318 PELOriginalPeriodKernelConnection318
open PELOriginalMovingKernelConnection318 PELOriginalSecondFundamentalMetric318
open PELOriginalUnitFlatTransport318 PELOriginalFlatPeriodSquare318
open PELOriginalFlatSymplecticTransport318

lemma kernel_recover (τ : ℂ) (p : Ambient) (hp : periodMap τ p=0) :
    kernelLift τ p.2=p := by
  apply Prod.ext
  · exact (eq_neg_of_add_eq_zero_left hp).symm
  · rfl
lemma arbitrary_kernel_pairing (τ : ℂ) (hτ : τ≠0) (p : Ambient)
    (hp : periodMap τ p=0) (s : ℂ → Ambient) (s' : Ambient) (hs : HasDerivAt s s' τ)
    (hk : ∀ᶠ z in 𝓝 τ, periodMap z (s z)=0) :
    symplectic p (deriv s τ)=secondPairing τ p.2 (s τ).2 := by
  have he : s =ᶠ[𝓝 τ] (fun z => kernelLift z (s z).2) := by
    filter_upwards [hk] with z hz
    exact (kernel_recover z (s z) hz).symm
  have hv : HasDerivAt (fun z => (s z).2) s'.2 τ :=
    (ContinuousLinearMap.snd ℂ ComplexVectors ComplexVectors).hasFDerivAt.comp_hasDerivAt τ hs
  conv_lhs => rw [←kernel_recover τ p hp]
  rw [he.deriv_eq]
  exact moving_pairing τ hτ p.2 (fun z => (s z).2) s'.2 hv

/-- Genuine both-inverse frame transition induced by the original
constant integral monodromy on the two whole period-kernel planes. -/
@[expose] def coefficientEquiv (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : ComplexVectors ≃ₗ[ℂ] ComplexVectors where
  toFun v := (transport u.val (kernelLift (parameter u τ) v)).2
  invFun v := ((transport u.val).symm (kernelLift τ v)).2
  left_inv := by
    intro v
    have hk := (kernel_transport u τ hτ (kernelLift (parameter u τ) v)).mpr
      (kernelLift_period _ v)
    rw [kernel_recover τ _ hk,LinearEquiv.symm_apply_apply]
    rfl
  right_inv := by
    intro v
    have hk := (kernel_transport u τ hτ ((transport u.val).symm (kernelLift τ v))).mp
      (by rw [LinearEquiv.apply_symm_apply];exact kernelLift_period τ v)
    rw [kernel_recover (parameter u τ) _ hk,LinearEquiv.apply_symm_apply]
    rfl
  map_add' := by intro v w;simpa only [map_add]
  map_smul' := by intro a v;simpa only [map_smul]

/-- Full original second-fundamental tensor covariance under ACTUAL
norm-one monodromy. The base derivative is retained, rather than hidden
inside a fiberwise matching or replaced by a scalar of equal norm. -/
theorem secondPairing_covariance (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (v w : ComplexVectors) :
    secondPairing τ (coefficientEquiv u τ hτ v) (coefficientEquiv u τ hτ w)=
      deriv (parameter u) τ*secondPairing (parameter u τ) v w := by
  have hγ := MobiusPoincarePullback318.hasDerivAt_mobius
    (QuaternionicUnitPeriodTransport318.unitMatrix PELQuaternionRealRepresentation318.representation
      PELPrincipalOrderCoordinates318.order u.val) u.property τ hτ
  let F : ℂ → Ambient := fun z => kernelLift (parameter u z) w
  have hF := (hasDerivAt_kernelLift (parameter u τ)
    (parameter_ne _ (parameter_positive u τ hτ)) w).scomp τ hγ
  let S : ℂ → Ambient := fun z => transport u.val (F z)
  have hS := hasDerivAt_transport u F _ τ hF
  have hd : deriv S τ=transport u.val (deriv F τ) := by
    rw [hS.deriv,hF.deriv]
  have hk : ∀ᶠ z in 𝓝 τ, periodMap z (S z)=0 := by
    have ho : IsOpen {z : ℂ | 0<z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [ho.mem_nhds hτ] with z hz
    exact (kernel_transport u z hz (F z)).mpr (kernelLift_period _ w)
  have hp := (kernel_transport u τ hτ (kernelLift (parameter u τ) v)).mpr
    (kernelLift_period _ v)
  have ht := arbitrary_kernel_pairing τ (parameter_ne τ hτ)
    (transport u.val (kernelLift (parameter u τ) v)) hp S _ hS hk
  change symplectic (transport u.val (kernelLift (parameter u τ) v)) (deriv S τ)=
    secondPairing τ (coefficientEquiv u τ hτ v) (coefficientEquiv u τ hτ w) at ht
  rw [←ht,hd,symplectic_transport]
  exact pulledPairing_formula (parameter u) τ hγ.differentiableAt
    (parameter_positive u τ hτ) v w
end PELOriginalKernelMonodromyCovariance318
