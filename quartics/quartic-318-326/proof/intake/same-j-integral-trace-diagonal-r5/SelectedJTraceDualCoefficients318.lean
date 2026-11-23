module
public import Mathlib.RingTheory.Trace.Basic

public section
noncomputable section

namespace SelectedJTraceDualCoefficients318

open Algebra Module

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]

private theorem repr_trace (b : Basis ι K L) (x : L) (i : ι) :
    b.repr x i = trace K L (x * b.traceDual i) := by
  simpa only [Module.Basis.traceDual_traceDual, traceForm_apply] using
    (b.traceDual).traceDual_repr_apply x i

/-- The multiplication matrix in the trace-dual basis is the transpose of
the multiplication matrix in the original basis. -/
theorem traceDual_repr_mul (b : Basis ι K L) (x : L) (i j : ι) :
    b.traceDual.repr (x * b.traceDual i) j = b.repr (x * b j) i := by
  rw [Module.Basis.traceDual_repr_apply, traceForm_apply, repr_trace]
  congr 1
  ac_rfl

/-- Multiplication of the two entries of the trace Casimir gives one. This
is a trace-of-multiplication argument, not a division by the field degree. -/
theorem sum_mul_traceDual (b : Basis ι K L) :
    (∑ i, b i * b.traceDual i) = 1 := by
  have eqtrace (z : L) :
      trace K L (z * (∑ i, b i * b.traceDual i)) = trace K L z := by
    rw [Finset.mul_sum, map_sum, Algebra.trace_eq_matrix_trace b z, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [repr_trace, mul_assoc]
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate K L).1
  intro z
  rw [traceForm_apply, sub_mul, map_sub, one_mul, mul_comm (∑ i, b i * b.traceDual i) z,
    eqtrace, sub_self]

end SelectedJTraceDualCoefficients318

#print axioms SelectedJTraceDualCoefficients318.traceDual_repr_mul
#print axioms SelectedJTraceDualCoefficients318.sum_mul_traceDual
