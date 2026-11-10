module
public import PELFixedNormalizerStrictTrace318
public section
noncomputable section
namespace PELOriginalFixedTangent318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open QuaternionicFixedParameter318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledComplexBase318
open PELUnlevelledNormalizerAction318 PELPrincipalThreeStabilizer318 PELOriginalElementaryAction318
open PELInertiaArithmeticFixedPoints318 PELNontrivialFixedTraceZero318 PELFixedNormalizerLift318
set_option maxHeartbeats 1800000

/-- Exact trace-zero fixed-line identity on the literal original matrix.
It does not assume the fixed parameter is one of the five displayed CM points. -/
theorem denominator_square (M : RealMatrices) (τ : ℂ) (hf : fixesLine M τ)
    (ht : M 0 0+M 1 1=0) : denominator M τ^2= -(M.det:ℂ) := by
  have htC : (M 0 0:ℂ)+(M 1 1:ℂ)=0 := by exact_mod_cast ht
  have hd : (M.det:ℂ)=(M 0 0:ℂ)*(M 1 1:ℂ)-(M 0 1:ℂ)*(M 1 0:ℂ) := by
    rw [Matrix.det_fin_two]
    push_cast <;> rfl
  rw [hd]
  unfold denominator
  change (M 0 0:ℂ)*τ+(M 0 1:ℂ)=τ*((M 1 0:ℂ)*τ+(M 1 1:ℂ)) at hf
  linear_combination -(M 1 0:ℂ)*hf+((M 1 0:ℂ)*τ+(M 1 1:ℂ))*htC

/-- Every positive trace-zero matrix fixing an upper-half-plane point
has the actual complex derivative minus one there. -/
theorem trace_zero_derivative (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (hdet : 0<M.det) (hf : fixesLine M τ) (ht : M 0 0+M 1 1=0) :
    HasDerivAt (mobius M) (-1) τ := by
  have hden := QuaternionicPositiveDeterminant318.denominator_nonzero M hdet τ hτ
  have h := fractional_derivative (M 0 0:ℂ) (M 0 1:ℂ) (M 1 0:ℂ) (M 1 1:ℂ) τ hden
  have hd : (M 0 0:ℂ)*(M 1 1:ℂ)-(M 0 1:ℂ)*(M 1 0:ℂ)=(M.det:ℂ) := by
    rw [Matrix.det_fin_two]
    push_cast <;> rfl
  change HasDerivAt (mobius M)
    (((M 0 0:ℂ)*(M 1 1:ℂ)-(M 0 1:ℂ)*(M 1 0:ℂ))/denominator M τ^2) τ at h
  rw [hd,denominator_square M τ hf ht] at h
  have hn : (M.det:ℂ)≠0 := by exact_mod_cast hdet.ne'
  have he : (M.det:ℂ)/ -(M.det:ℂ)= -1 := by field_simp
  rwa [he] at h

/-- At EVERY actual fixed point of a nontrivial original label, the SAME
coarse automorphism has an upstairs-fixed lift with derivative minus one.
This is not yet an algebraic ramification-index assertion. -/
theorem original_fixed_tangent (v : InertiaLabels318.V) (hv : v≠0) (τ : HalfPlane)
    (hf : Multiplicative.ofAdd v • projection τ=projection τ) :
    ∃ n : positiveNormalizer,baseAction n τ=τ ∧
      (∀ x,coarseAction n x=Multiplicative.ofAdd v • x) ∧
      HasDerivAt (mobius (PELPositiveNormalizerMobius318.matrix n)) (-1) (τ:ℂ) := by
  obtain ⟨n,hn,ht,hp⟩ := fixed_trace_zero v hv τ hf
  refine ⟨n,hn,?_,?_⟩
  · intro x
    rw [PELFullNormalizerAction318.actual_action_factorization,hp]
  · apply trace_zero_derivative _ τ τ.property (matrix_positive n)
    · exact fixesLine_of_mobius _ _
        (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive n) τ τ.property)
        (congrArg Subtype.val hn)
    · change representation (n.val:B) 0 0+representation (n.val:B) 1 1=0
      rw [representation_trace,ht] <;> norm_num
end PELOriginalFixedTangent318
