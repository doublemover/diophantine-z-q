module
public import PELFixedNormalizerLift318
public section
noncomputable section
namespace PELNontrivialFixedTraceZero318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPositiveOrderNormalizer318
open PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELScalarCoarseKernel318 PELOriginalElementaryAction318 PELFixedNormalizerLift318
set_option maxHeartbeats 1800000

/-- Quaternion square scalarity plus nonzero trace forces an actual
rational scalar, retaining all three original imaginary coordinates. -/
theorem scalar_of_square_scalar (x : B) (q : ℚ) (hs : x*x=algebraMap ℚ B q)
    (ht : reducedTrace x≠0) : x=algebraMap ℚ B x.re := by
  have hI := congrArg (fun y : B => y.imI) hs
  have hJ := congrArg (fun y : B => y.imJ) hs
  have hK := congrArg (fun y : B => y.imK) hs
  simp [QuaternionAlgebra.algebraMap_eq] at hI hJ hK
  have hr : x.re≠0 := by
    intro h
    apply ht
    simp [reducedTrace,h]
  have h2 : (2:ℚ)*x.re≠0 := mul_ne_zero (by norm_num) hr
  have hi : (2*x.re)*x.imI=0 := by linear_combination hI
  have hj : (2*x.re)*x.imJ=0 := by linear_combination hJ
  have hk : (2*x.re)*x.imK=0 := by linear_combination hK
  have hi0 := (mul_eq_zero.mp hi).resolve_left h2
  have hj0 := (mul_eq_zero.mp hj).resolve_left h2
  have hk0 := (mul_eq_zero.mp hk).resolve_left h2
  ext <;> simp [QuaternionAlgebra.algebraMap_eq,hi0,hj0,hk0]

theorem positive_trace_zero_imI (x : B) (hn : 0<reducedNorm x) (ht : reducedTrace x=0) : x.imI≠0 := by
  have hr : x.re=0 := by unfold reducedTrace at ht; linarith
  intro hi
  rw [reducedNorm,hr,hi] at hn
  nlinarith [sq_nonneg x.imJ,sq_nonneg x.imK]

theorem positive_trace_zero_lower_left (M : RealMatrices) (hd : 0<M.det)
    (ht : M 0 0+M 1 1=0) : M 1 0≠0 := by
  intro hc
  rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
  have he : M 1 1= -M 0 0 := by linarith
  rw [he] at hd
  nlinarith [sq_nonneg (M 0 0)]

theorem label_add_self (v : InertiaLabels318.V) : v+v=0 := by
  ext i
  have h (z : ZMod 2) : z+z=0 := by fin_cases z <;> decide
  exact h (v i)

/-- A nontrivial original label fixing a coarse point has an upstairs
trace-zero representative. This is derived from its ACTUAL order-two action,
not postulated from a labeled inertia table. -/
theorem fixed_trace_zero (v : InertiaLabels318.V) (hv : v≠0) (τ : HalfPlane)
    (h : coarseAction (word v) (projection τ)=projection τ) :
    ∃ n : positiveNormalizer,baseAction n τ=τ ∧ reducedTrace (n.val:B)=0 ∧
      PELPositiveOrderNormalizer318.parity n=Multiplicative.ofAdd v := by
  obtain ⟨n,hnfix,hna,hnp⟩ := original_fixed_lift (word v) τ h
  have hp : PELPositiveOrderNormalizer318.parity n=Multiplicative.ofAdd v := hnp.trans (parity_word v)
  have hnn : ∀ x,coarseAction (n*n) x=x := by
    intro x
    rw [coarseAction_mul,hna,hna,←word_action_add,label_add_self,word_action_zero]
  have hnnfix : baseAction (n*n) τ=τ := by rw [baseAction_mul,hnfix,hnfix]
  obtain ⟨q,hq,hs⟩ := scalar_of_coarse_identity_and_fixed (n*n) τ hnn hnnfix
  refine ⟨n,hnfix,?_,hp⟩
  by_contra ht
  have hx : (n.val:B)=algebraMap ℚ B (n.val:B).re := scalar_of_square_scalar (n.val:B) q hs ht
  have hr : (n.val:B).re≠0 := by
    intro hr
    have hn0 := Units.ne_zero n.val
    apply hn0
    rw [hx,hr,map_zero]
  have hu : n.val=PELQuaternionNormParity318.scalarUnit (Units.mk0 (n.val:B).re hr) := by
    apply Units.ext
    exact hx
  have hz : PELPositiveOrderNormalizer318.parity n=1 := by
    change PELQuaternionNormParity318.parityHom n.val=1
    rw [hu]
    exact PELInertiaRationalConjugacy318.scalar_parity _
  apply hv
  exact congrArg Multiplicative.toAdd (hp.symm.trans hz)
end PELNontrivialFixedTraceZero318
