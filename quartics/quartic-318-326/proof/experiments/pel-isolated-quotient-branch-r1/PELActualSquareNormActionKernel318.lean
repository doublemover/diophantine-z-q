module
public import PELOriginalWordActionFaithful318
public import PELSquareNormNormalizerKernel318
public section
noncomputable section
namespace PELActualSquareNormActionKernel318
open QuaternionicJointPeriodTopology318 PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELNormOneBaseAction318 PELEffectiveNormOneAction318 PELUnlevelledComplexBase318
open PELOriginalPrimeBaseInvolutions318 PELScalarCoarseKernel318 PELJointNormOneAction318
set_option maxHeartbeats 1800000

/-- The genuine analytic kernel supplies an actual rational square norm.
This direction is obtained from its local lift, not from four prime parities. -/
theorem identity_has_square_norm (g : positiveNormalizer) (hid : ∀ x,coarseAction g x=x) :
    ∃ q : ℚˣ,reducedNorm (g.val:B)=(q:ℚ)^2 := by
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
  have hu1 : reducedNorm ((originalNormalizer u).val:B)=1 :=
    (mem_normOneUnits u.val).mp u.property
  have hui : reducedNorm (((originalNormalizer u).val⁻¹:Bˣ):B)=1 := by
    have hh : reducedNorm ((originalNormalizer u).val:B)*
        reducedNorm (((originalNormalizer u).val⁻¹:Bˣ):B)=1 := by
      rw [←PELQuaternionNormParity318.norm_mul,Units.val_inv] <;> norm_num [reducedNorm]
    rwa [hu1,one_mul] at hh
  have hnN : reducedNorm (n.val:B)=reducedNorm (g.val:B) := by
    change reducedNorm ((((originalNormalizer u).val⁻¹:Bˣ):B)*(g.val:B))= _
    rw [PELQuaternionNormParity318.norm_mul,hui,one_mul]
  refine ⟨Units.mk0 q hq0,?_⟩
  change reducedNorm (g.val:B)=q^2
  rw [←hnN,hs,PELQuaternionNormParity318.norm_scalar]

/-- The converse uses the actual square-norm normalizer factorization in
the SAME original integral order. No parity-support premise is substituted. -/
theorem square_norm_identity (g : positiveNormalizer) (q : ℚˣ)
    (hN : reducedNorm (g.val:B)=(q:ℚ)^2) : ∀ x,coarseAction g x=x := by
  obtain ⟨v,hv,he⟩ := PELSquareNormNormalizerKernel318.square_norm_factorization
    ⟨g.val,g.property.1⟩ q hN
  let u : normOneUnits := ⟨v,(mem_normOneUnits v).mpr hv⟩
  have hs : (g.val:B)=(q:ℚ) • ((originalNormalizer u).val:B) := by
    have hh := congrArg (fun x : Bˣ => (x:B)) he
    change (g.val:B)=algebraMap ℚ B (q:ℚ)*((v:order):B) at hh
    simpa only [Algebra.smul_def] using hh
  intro x
  rw [scalar_related_action g (originalNormalizer u) (q:ℚ) q.ne_zero hs]
  exact norm_one_trivial u x

/-- Exact kernel theorem for the ACTUAL holomorphic action on the literal
unlevelled base. Four-prime parity-zero⇒square and the classification of the
whole normalizer quotient remain separate. -/
theorem actual_action_kernel_iff (g : positiveNormalizer) :
    (∀ x,coarseAction g x=x) ↔ ∃ q : ℚˣ,reducedNorm (g.val:B)=(q:ℚ)^2 :=
  ⟨identity_has_square_norm g,fun ⟨q,hq⟩ => square_norm_identity g q hq⟩
end PELActualSquareNormActionKernel318
