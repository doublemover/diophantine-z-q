module
public import PELOriginalLabeledFixedOrbits318
public section
noncomputable section
namespace PELFixedNormalizerLift318
open QuaternionicJointPeriodTopology318 PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318 PELNormOneBaseAction318
open PELEffectiveNormOneAction318 PELOriginalPrimeBaseInvolutions318 PELJointNormOneAction318
set_option maxHeartbeats 1600000

/-- An ACTUAL fixed coarse point supplies an upstairs-fixed normalizer
with the SAME action and original parity, after a genuine norm-one orbit lift. -/
theorem original_fixed_lift (g : positiveNormalizer) (τ : HalfPlane)
    (h : coarseAction g (projection τ)=projection τ) :
    ∃ n : positiveNormalizer,baseAction n τ=τ ∧
      (∀ x,coarseAction n x=coarseAction g x) ∧
      PELPositiveOrderNormalizer318.parity n=PELPositiveOrderNormalizer318.parity g := by
  rw [coarseAction_square] at h
  obtain ⟨v,hv⟩ := covering.apply_eq_iff_mem_orbit.mp h
  obtain ⟨u,hu⟩ := effectiveMap_surjective v
  have he : baseAction (originalNormalizer u) τ=baseAction g τ := by
    rw [←hu] at hv
    exact hv
  let n : positiveNormalizer := (originalNormalizer u)⁻¹*g
  have hi : ∀ x,coarseAction (originalNormalizer u)⁻¹ x=x := by
    intro x
    have hh := norm_one_trivial u (coarseAction (originalNormalizer u)⁻¹ x)
    rw [←coarseAction_mul,mul_inv_cancel,coarseAction_one] at hh
    exact hh.symm
  refine ⟨n,?_,?_,?_⟩
  · change baseAction ((originalNormalizer u)⁻¹*g) τ=τ
    rw [baseAction_mul,←he,←baseAction_mul,inv_mul_cancel,baseAction_one]
  · intro x
    change coarseAction ((originalNormalizer u)⁻¹*g) x=coarseAction g x
    rw [coarseAction_mul,hi]
  · have hp : PELPositiveOrderNormalizer318.parity (originalNormalizer u)=1 :=
      PELQuaternionNormParity318.parity_norm_one u.val ((mem_normOneUnits _).mp u.property)
    change PELPositiveOrderNormalizer318.parity ((originalNormalizer u)⁻¹*g)= _
    rw [map_mul,map_inv,hp,inv_one,one_mul]
end PELFixedNormalizerLift318
