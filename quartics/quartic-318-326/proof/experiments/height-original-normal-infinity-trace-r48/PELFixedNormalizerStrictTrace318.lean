module
public import PELFullNormalizerAction318
public section
noncomputable section
namespace PELFixedNormalizerStrictTrace318
open QuaternionicRealPeriod318 QuaternionicFixedParameter318 QuaternionicJointPeriodTopology318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalThreeStabilizer318
open PELPeriodDeterminant318 PELScalarCoarseKernel318 PELPositiveOrderNormalizer318
open PELPositiveNormalizerMobius318
set_option maxHeartbeats 1600000

/-- Equality in the genuine upper-half-plane trace bound is scalarity,
without any determinant-one normalization or square-root rescaling. -/
theorem scalar_of_trace_equality (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (hf : fixesLine M τ) (he : (M 0 0+M 1 1)^2=4*M.det) :
    M=M 1 1 • (1:RealMatrices) := by
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ hf
  have hs := determinant_squares M τ hτ hf
  have hc : M 1 0*τ.im=0 := by
    rw [ha,hs] at he
    nlinarith [sq_nonneg (M 1 0*τ.im)]
  have hc0 : M 1 0=0 := (mul_eq_zero.mp hc).resolve_right hτ.ne'
  have ha0 : M 0 0=M 1 1 := by simpa only [hc0,mul_zero,zero_mul,add_zero] using ha
  have hb0 : M 0 1=0 := by simpa only [hc0,neg_zero,zero_mul] using hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply,Matrix.one_apply,ha0,hb0,hc0]

/-- Strict trace bound on the SAME rational quaternion fixing the actual
upper-half-plane line. No abstract elliptic conjugacy classification is used. -/
theorem original_strict_trace (x : B) (τ : ℂ) (hτ : 0<τ.im)
    (hf : fixesLine (representation x) τ)
    (hn : x≠algebraMap ℚ B x.re) : reducedTrace x^2<4*reducedNorm x := by
  have hb := trace_bound (representation x) τ hτ hf
  have hs : (representation x 0 0+representation x 1 1)^2<4*(representation x).det := by
    by_contra hnot
    have he := le_antisymm hb (le_of_not_gt hnot)
    exact hn (rational_scalar_of_matrix x _ (scalar_of_trace_equality _ τ hτ hf he))
  rw [representation_trace,representation_det] at hs
  exact_mod_cast hs

/-- A nontrivial original parity fixing upstairs satisfies the strict
bound. Scalar signs and every other rational scalar are excluded by the SAME
actual parity character, not by a chosen matrix representative. -/
theorem fixed_nontrivial_parity (g : positiveNormalizer) (τ : HalfPlane)
    (hf : baseAction g τ=τ) (hp : PELPositiveOrderNormalizer318.parity g≠1) :
    reducedTrace (g.val:B)^2<4*reducedNorm (g.val:B) := by
  apply original_strict_trace (g.val:B) τ τ.property
  · exact fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive g) τ τ.property)
      (congrArg Subtype.val hf)
  · intro hs
    have hr : (g.val:B).re≠0 := by
      intro hz
      apply Units.ne_zero g.val
      rw [hs,hz,map_zero]
    have hu : g.val=PELQuaternionNormParity318.scalarUnit (Units.mk0 (g.val:B).re hr) := by
      apply Units.ext
      exact hs
    apply hp
    change PELQuaternionNormParity318.parityHom g.val=1
    rw [hu]
    exact PELInertiaRationalConjugacy318.scalar_parity _
end PELFixedNormalizerStrictTrace318
