module
public import PELNormalizerArithmeticBase318
public import Mathlib.Analysis.Calculus.Deriv.Inv
public section
noncomputable section
namespace PELInertiaArithmeticFixedPoints318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELNormalizerArithmeticBase318
open PELPrincipalThreeCovering318 PELInertiaNormalizerData318 PELInertiaRealFixedPoints318
set_option maxHeartbeats 1400000

@[expose] def originalFixedPoint (i : Fin 5) : HalfPlane :=
  ⟨fixedPoint i,fixedPoint_im_positive i⟩

theorem original_fixed (i : Fin 5) :
    baseAction (inertiaElement i) (originalFixedPoint i)=originalFixedPoint i := by
  apply Subtype.ext
  exact fixedPoint_equation i

/-- These are actual fixed points on the fine principal-three base. They
are not yet identified with the five branch points on the maximal-level curve. -/
theorem arithmetic_fixed (i : Fin 5) :
    arithmeticAction (inertiaElement i) (baseQuotient (originalFixedPoint i))=
      baseQuotient (originalFixedPoint i) := by
  rw [arithmeticAction_square,original_fixed]

/-- A generic derivative lemma fixes the field/module spine before its
application to the original complex splitting. -/
theorem fractional_derivative {K : Type*} [NontriviallyNormedField K]
    (a b c d z : K) (h : c*z+d≠0) :
    HasDerivAt (fun w => (a*w+b)/(c*w+d)) ((a*d-b*c)/(c*z+d)^2) z := by
  have hn : HasDerivAt (fun w : K => a*w+b) a z := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id z).const_mul a).add_const b
  have hd : HasDerivAt (fun w : K => c*w+d) c z := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id z).const_mul c).add_const d
  convert hn.div hd h using 1 <;> congr 1 <;> ring

theorem original_denominator_square (i : Fin 5) :
    denominator (matrix (inertiaElement i)) (fixedPoint i)^2= -(discriminant i:ℂ) := by
  change ((PELQuaternionRealRepresentation318.representation (element i) 1 0:ℂ)*fixedPoint i+
    (PELQuaternionRealRepresentation318.representation (element i) 1 1:ℂ))^2= _
  rw [matrix_trace_zero]
  push_cast
  change ((C i:ℂ)*fixedPoint i-(A i:ℂ))^2= _
  rw [denominator_value,mul_pow,Complex.I_sq]
  have hs : (Real.sqrt (discriminant i:ℝ):ℂ)^2=(discriminant i:ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt (discriminant_real_positive i))
  rw [hs,mul_neg_one]

/-- The actual upstairs tangent action is minus one at each displayed
original fixed point. No branch-index or complete stabilizer claim is inferred. -/
theorem original_derivative (i : Fin 5) :
    HasDerivAt (mobius (matrix (inertiaElement i))) (-1) (fixedPoint i) := by
  have hd := QuaternionicPositiveDeterminant318.denominator_nonzero
    (matrix (inertiaElement i)) (matrix_positive (inertiaElement i))
    (fixedPoint i) (fixedPoint_im_positive i)
  have h := fractional_derivative (matrix (inertiaElement i) 0 0:ℂ)
    (matrix (inertiaElement i) 0 1:ℂ) (matrix (inertiaElement i) 1 0:ℂ)
    (matrix (inertiaElement i) 1 1:ℂ) (fixedPoint i) hd
  have hdet : (matrix (inertiaElement i) 0 0:ℂ)*(matrix (inertiaElement i) 1 1:ℂ)-
      (matrix (inertiaElement i) 0 1:ℂ)*(matrix (inertiaElement i) 1 0:ℂ)=
      (discriminant i:ℂ) := by
    have hm : (matrix (inertiaElement i)).det=(discriminant i:ℝ) := by
      change (PELQuaternionRealRepresentation318.representation (element i)).det= _
      rw [PELPeriodDeterminant318.representation_det,element_norm]
      norm_num
    rw [Matrix.det_fin_two] at hm
    exact_mod_cast hm
  change HasDerivAt (mobius (matrix (inertiaElement i)))
    (((matrix (inertiaElement i) 0 0:ℂ)*(matrix (inertiaElement i) 1 1:ℂ)-
      (matrix (inertiaElement i) 0 1:ℂ)*(matrix (inertiaElement i) 1 0:ℂ))/
      denominator (matrix (inertiaElement i)) (fixedPoint i)^2) (fixedPoint i) at h
  rw [hdet,original_denominator_square] at h
  have hn : (discriminant i:ℂ)≠0 := by exact_mod_cast (discriminant_real_positive i).ne'
  have he : (discriminant i:ℂ)/ -(discriminant i:ℂ)= -1 := by field_simp
  rwa [he] at h
end PELInertiaArithmeticFixedPoints318
