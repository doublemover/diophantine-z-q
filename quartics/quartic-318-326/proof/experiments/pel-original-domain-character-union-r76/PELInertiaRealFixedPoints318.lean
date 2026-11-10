module
public import PELInertiaQuadraticEmbeddings318
public section
noncomputable section
namespace PELInertiaRealFixedPoints318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELInertiaNormalizerData318 PELQuaternionRealRepresentation318
set_option maxHeartbeats 1400000

@[expose] def A (i : Fin 5) : ℝ := representation (element i) 0 0
@[expose] def Bentry (i : Fin 5) : ℝ := representation (element i) 0 1
@[expose] def C (i : Fin 5) : ℝ := representation (element i) 1 0

theorem matrix_trace_zero (i : Fin 5) : representation (element i) 1 1= -A i := by
  fin_cases i <;> norm_num [A,representation,matrix,element,coefficients,embed]

theorem determinant_identity (i : Fin 5) :
    -(A i)^2-Bentry i*C i=(discriminant i:ℝ) := by
  fin_cases i <;>
    norm_num [A,Bentry,C,representation,matrix,element,coefficients,embed,discriminant] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

/-- The chosen signs fix the actual upper-half-plane component. -/
theorem lower_left_positive (i : Fin 5) : 0<C i := by
  have hb : beta<3 := by nlinarith [beta_sq,beta_pos]
  have h1 : 0<(3/2:ℝ)-beta/2 := by linarith
  have h2 : 0<(1/2:ℝ)-beta/10 := by linarith
  have h3 : 0<(5/2:ℝ)-beta/2 := by linarith
  have h4 : 0<(4:ℝ)-beta := by linarith
  fin_cases i
  · convert mul_pos alpha_pos h1 using 1 <;>
      norm_num [C,representation,matrix,element,coefficients,embed] <;> ring
  · convert mul_pos alpha_pos h2 using 1 <;>
      norm_num [C,representation,matrix,element,coefficients,embed] <;> ring
  · convert mul_pos alpha_pos h3 using 1 <;>
      norm_num [C,representation,matrix,element,coefficients,embed] <;> ring
  · convert mul_pos alpha_pos h4 using 1 <;>
      norm_num [C,representation,matrix,element,coefficients,embed] <;> ring
  · simpa [C,representation,matrix,element,coefficients,embed] using alpha_pos

@[expose] def fixedPoint (i : Fin 5) : ℂ :=
  ⟨A i/C i,Real.sqrt (discriminant i:ℝ)/C i⟩

theorem discriminant_real_positive (i : Fin 5) : 0<(discriminant i:ℝ) := by
  fin_cases i <;> norm_num [discriminant]

theorem fixedPoint_im_positive (i : Fin 5) : 0<(fixedPoint i).im :=
  div_pos (Real.sqrt_pos.mpr (discriminant_real_positive i)) (lower_left_positive i)

/-- The denominator is the specific positive imaginary eigenvalue. -/
theorem denominator_value (i : Fin 5) :
    (C i:ℂ)*fixedPoint i-(A i:ℂ)=
      (Real.sqrt (discriminant i:ℝ):ℂ)*Complex.I := by
  have hc := ne_of_gt (lower_left_positive i)
  apply Complex.ext <;>
    simp [fixedPoint,Complex.mul_re,Complex.mul_im] <;> field_simp [hc]

theorem denominator_ne_zero (i : Fin 5) :
    (C i:ℂ)*fixedPoint i-(A i:ℂ)≠0 := by
  rw [denominator_value]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (discriminant_real_positive i))
  · exact Complex.I_ne_zero

/-- Exact fixed-point relation for the original split-real matrix. No
identification with any prescribed contact-curve branch coordinate is made. -/
theorem fixedPoint_equation (i : Fin 5) :
    ((representation (element i) 0 0:ℂ)*fixedPoint i+
      (representation (element i) 0 1:ℂ))/
      ((representation (element i) 1 0:ℂ)*fixedPoint i+
        (representation (element i) 1 1:ℂ))=fixedPoint i := by
  rw [matrix_trace_zero]
  change ((A i:ℂ)*fixedPoint i+(Bentry i:ℂ))/
    ((C i:ℂ)*fixedPoint i-(A i:ℂ))=fixedPoint i
  apply (div_eq_iff (denominator_ne_zero i)).2
  rw [denominator_value]
  have hc := ne_of_gt (lower_left_positive i)
  have hs := Real.sq_sqrt (le_of_lt (discriminant_real_positive i))
  have hd := determinant_identity i
  apply Complex.ext
  · simp [fixedPoint,Complex.mul_re,Complex.mul_im]
    field_simp [hc]
    nlinarith
  · simp [fixedPoint,Complex.mul_re,Complex.mul_im]
    ring
end PELInertiaRealFixedPoints318
