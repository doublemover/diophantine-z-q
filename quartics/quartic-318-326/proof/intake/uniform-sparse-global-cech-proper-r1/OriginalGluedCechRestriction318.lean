module
public import OriginalGluedDualizingTransition318
public section
noncomputable section
namespace OriginalGluedCechRestriction318
open Polynomial OriginalSparseQuadraticCharts318 OriginalActualQuadraticLaurent318
open OriginalGluedDualizingTransition318 OriginalGlobalDualizingClass318 OriginalGlobalP1Residue318
variable {E:Type*} [Field E]

theorem inv_cu (p:E[X]) :
    LaurentPolynomial.invert (cu p)=aeval (LaurentPolynomial.T (-1)) p := by
  rw [cu,←aeval_xl]
  have e:=aeval_algHom_apply (LaurentPolynomial.invert (R:=E)).toAlgHom (Xl:LaurentPolynomial E) p
  change _=LaurentPolynomial.invert (aeval (Xl:LaurentPolynomial E) p) at e
  rw [←e]
  change aeval (LaurentPolynomial.invert (LaurentPolynomial.T 1)) p=_
  rw [LaurentPolynomial.invert_T]

/-- Weight of the relative monogenic generator on a genuine overlap:
(v chart) λ_w dv ↦ −x λ_y dx. The scalar −x is forced by the base
transition dv=−x⁻² dx and the codifferent transition w=y/x³. -/
theorem generator_transition (s t:E) (b:D (G s t)) :
    -(LaurentPolynomial.T (1:ℤ)*OriginalQuadraticDualizing318.lambda (toLaurent (F s t)) (move s t b)) =
      -(LaurentPolynomial.T (-2)*LaurentPolynomial.invert (OriginalQuadraticDualizing318.lambda (toLaurent (G s t)) b)) := by
  rw [lambda_move,←mul_assoc,←LaurentPolynomial.T_add]
  rfl

@[expose] def construct (f:E[X]) (a b:OriginalActualQuadraticLaurent318.L E) : D f := inc f a+inc f b*Y f
theorem inc_eq (f:E[X]) (a:LaurentPolynomial E) : inc f a=algebraMap _ (D f) a := rfl
theorem everyone (f:E[X]) (z:D f) : ∃ a b:OriginalActualQuadraticLaurent318.L E, construct f a b=z := by
  refine ⟨((OriginalQuadraticDualizing318.basis (toLaurent f)).repr z) 0,OriginalQuadraticDualizing318.lambda (toLaurent f) z,?_⟩
  rw [construct,inc_eq,inc_eq]
  simpa only [Algebra.smul_def,mul_one] using OriginalQuadraticDualizing318.decompose (toLaurent f) z

/-- These are the actual images of the reciprocal affine regular sections via
the SAME ring map used to glue the curve. Together with ordinary restriction
this justifies the source map whose cokernel is computed by traceClass. -/
theorem restricted (s t:E) (a b:E[X]) :
    -(inc (F s t) (LaurentPolynomial.T 1)*move s t (construct (G s t) (cu a) (cu b)))=
      construct (F s t) (cvOdd a) (cv b) := by
  unfold construct
  rw [map_add,map_mul,base_move,base_move,y_move,inv_cu,inv_cu]
  unfold cvOdd cv
  simp only [map_neg,map_mul]
  have e : inc (F s t) (LaurentPolynomial.T 1)*inc (F s t) (LaurentPolynomial.T (-3))=
      inc (F s t) (LaurentPolynomial.T (-2)) := by
    rw [←map_mul,←LaurentPolynomial.T_add]
    rfl
  linear_combination -(inc (F s t) (aeval (LaurentPolynomial.T (-1)) b))*(Y (F s t))*e

/-- Coherent finite trace of any localized regular coefficient, evaluated at 1.
This is the raw dualizing counit, not the trace divided by the fibre degree. -/
theorem eval_one (f:E[X]) (a b:OriginalActualQuadraticLaurent318.L E) :
    OriginalQuadraticDualizing318.toDual (toLaurent f) (construct f a b) 1=b := by
  change OriginalQuadraticDualizing318.lambda (toLaurent f) ((inc f a+inc f b*Y f)*1)=_
  rw [mul_one,map_add]
  rw [inc_eq,inc_eq,←Algebra.smul_def]
  rw [OriginalQuadraticDualizing318.lambda_base,map_smul,OriginalQuadraticDualizing318.lambda_y,
    zero_add,smul_eq_mul,mul_one]
end OriginalGluedCechRestriction318
#print axioms OriginalGluedCechRestriction318.restricted
#print axioms OriginalGluedCechRestriction318.eval_one
