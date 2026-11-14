module
public import PELCoarseIdentityLocalLift318
public section
noncomputable section
namespace PELScalarCoarseKernel318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicLocalIdentityScalar318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELNormOneBaseAction318 PELEffectiveNormOneAction318 PELUnlevelledComplexBase318
open PELOriginalPrimeBaseInvolutions318 PELRealRationalProportionality318
open PELPrincipalThreeStabilizer318 PELCoarseIdentityLocalLift318
set_option maxHeartbeats 1800000

/-- A scalar matrix in the faithful original splitting comes from the
ACTUAL rational scalar x.re, not an arbitrary real scalar. -/
theorem rational_scalar_of_matrix (x : B) (e : ℝ) (h : representation x=e • (1:RealMatrices)) :
    x=algebraMap ℚ B x.re := by
  have h0 := congrArg (fun M : RealMatrices => M 0 0) h
  have h1 := congrArg (fun M : RealMatrices => M 1 1) h
  have ht := representation_trace x
  have he : (x.re:ℝ)=e := by
    simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_one,if_pos] at h0 h1
    rw [h0,h1] at ht
    change e+e=((2*x.re:ℚ):ℝ) at ht
    push_cast at ht
    linarith
  apply representation_injective
  rw [h]
  have hs : algebraMap ℚ B x.re=x.re • (1:B) := by simp only [Algebra.smul_def,mul_one]
  rw [hs,representation_rat_smul,map_one,he]

/-- If the actual coarse action is the identity and one original parameter
is fixed upstairs, the normalizer itself is a nonzero rational scalar. -/
theorem scalar_of_coarse_identity_and_fixed (g : positiveNormalizer) (τ : HalfPlane)
    (hid : ∀ x,coarseAction g x=x) (hfix : baseAction g τ=τ) :
    ∃ q : ℚ,q≠0 ∧ (g.val:B)=algebraMap ℚ B q := by
  have hm := scalar_of_local_identity (PELPositiveNormalizerMobius318.matrix g)
    (matrix_positive g) τ τ.property (local_complex_identity g τ hfix hid)
  have hs := rational_scalar_of_matrix (g.val:B) _ hm
  refine ⟨(g.val:B).re,?_,hs⟩
  intro hz
  have hg := Units.ne_zero g.val
  apply hg
  rw [hs,hz,map_zero]

/-- The kernel of the ACTUAL analytic coarse action has trivial original
norm parity. This direction uses a genuine local covering inverse and does
not assume arithmetic classification of all parity-zero normalizers. -/
theorem identity_has_trivial_parity (g : positiveNormalizer) (hid : ∀ x,coarseAction g x=x) :
    PELPositiveOrderNormalizer318.parity g=1 := by
  have hq : projection (baseAction g basePoint)=projection basePoint := by
    rw [←coarseAction_square,hid]
  obtain ⟨v,hv⟩ := covering.apply_eq_iff_mem_orbit.mp hq
  obtain ⟨u,hu⟩ := effectiveMap_surjective v
  have he : baseAction (originalNormalizer u) basePoint=baseAction g basePoint := by
    rw [←hu] at hv
    exact hv
  let n : positiveNormalizer := (originalNormalizer u)⁻¹*g
  have hnfix : baseAction n basePoint=basePoint := by
    change baseAction ((originalNormalizer u)⁻¹*g) basePoint=basePoint
    rw [baseAction_mul,←he,←baseAction_mul,inv_mul_cancel,baseAction_one]
  have hi : ∀ x,coarseAction (originalNormalizer u)⁻¹ x=x := by
    intro x
    have hh := norm_one_trivial u (coarseAction (originalNormalizer u)⁻¹ x)
    rw [←coarseAction_mul,mul_inv_cancel,coarseAction_one] at hh
    exact hh.symm
  have hn : ∀ x,coarseAction n x=x := by
    intro x
    change coarseAction ((originalNormalizer u)⁻¹*g) x=x
    rw [coarseAction_mul,hid,hi]
  obtain ⟨q,hq0,hs⟩ := scalar_of_coarse_identity_and_fixed n basePoint hn hnfix
  have hnu : n.val=PELQuaternionNormParity318.scalarUnit (Units.mk0 q hq0) := by
    apply Units.ext
    exact hs
  have hnpar : PELPositiveOrderNormalizer318.parity n=1 := by
    change PELQuaternionNormParity318.parityHom n.val=1
    rw [hnu]
    exact PELInertiaRationalConjugacy318.scalar_parity _
  have hupar : PELPositiveOrderNormalizer318.parity (originalNormalizer u)=1 :=
    PELQuaternionNormParity318.parity_norm_one u.val
      ((PELJointNormOneAction318.mem_normOneUnits _).mp u.property)
  change PELPositiveOrderNormalizer318.parity ((originalNormalizer u)⁻¹*g)=1 at hnpar
  simpa only [map_mul,map_inv,hupar,inv_one,one_mul] using hnpar
end PELScalarCoarseKernel318
