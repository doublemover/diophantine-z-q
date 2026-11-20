module
public import SelectedJOneExactMinorLoss318
import all SelectedJOneExactMinorLoss318
public section
noncomputable section
open NumberField SelectedJOneExactMinorLoss318
open scoped BigOperators

namespace SelectedBlowupSameMinor318

variable {L : Type*} [Field L] [NumberField L] (v : FinitePlace L)
local notation "O" => integralAt v

/-- The comparison coefficient and the upstairs evaluation multiply
in the actual local integral ring, preserving the same numerator. -/
theorem lift_integral_ratio (c tZ : O) (uMin uZ a : L)
    (comparison : uZ = (c:L)*uMin) (evaluation : uZ*(tZ:L) = a) :
    ∃ tMin : O, (tMin:L) = (c:L)*(tZ:L) ∧ uMin*(tMin:L) = a := by
  refine ⟨c*tZ,rfl,?_⟩
  change uMin*((c:L)*(tZ:L)) = a
  rw [←evaluation,comparison]
  ring

/-- The two actual integral evaluations differ by the diagonal of
the pointwise comparison coefficients, with the same ordered m,C
on both sides. This does not infer integrality of IMin by division. -/
theorem same_ordered_rows {g : ℕ}
    (m C : Matrix (Fin g) (Fin g) L)
    (uMin uZ : Fin g → L) (c : Fin g → O)
    (IMin IZ : Matrix (Fin g) (Fin g) O)
    (comparison : ∀ i, uZ i = (c i:L)*uMin i)
    (minFrame : baseMatrix v IMin = Matrix.diagonal uMin * m * C)
    (resFrame : baseMatrix v IZ = Matrix.diagonal uZ * m * C) :
    baseMatrix v IZ = Matrix.diagonal (fun i => (c i:L)) * baseMatrix v IMin := by
  have h : Matrix.diagonal uZ =
      Matrix.diagonal (fun i => (c i:L)) * Matrix.diagonal uMin := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext comparison)
  rw [resFrame,minFrame,h]
  simp only [Matrix.mul_assoc]

/-- The determinant loss changes by exactly the opposite row-frame
shift, so using the authentic stable frames does not alter the generic
minor contribution. All norms are the same genuine normalized v. -/
theorem exact_loss_shift {g : ℕ}
    (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
    (uMin uZ : Fin g → L) (uMin_ne : ∀ i, uMin i ≠ 0)
    (c : Fin g → O) (c_ne : ∀ i, (c i:L) ≠ 0)
    (IMin IZ : Matrix (Fin g) (Fin g) O)
    (comparison : ∀ i, uZ i = (c i:L)*uMin i)
    (minFrame : baseMatrix v IMin = Matrix.diagonal uMin * m * C)
    (resFrame : baseMatrix v IZ = Matrix.diagonal uZ * m * C) :
    0 ≤ (∑ i, -Real.log (v (c i:L))) ∧
      -Real.log (v (baseMatrix v IZ).det) =
        -Real.log (v (baseMatrix v IMin).det) + ∑ i, -Real.log (v (c i:L)) := by
  have uZ_ne (i : Fin g) : uZ i ≠ 0 := by rw [comparison]; exact mul_ne_zero (c_ne i) (uMin_ne i)
  have hc (i : Fin g) : 0 < v (c i:L) := v.1.pos_iff.mpr (c_ne i)
  have hu (i : Fin g) : 0 < v (uMin i) := v.1.pos_iff.mpr (uMin_ne i)
  have hrow (i : Fin g) :
      -Real.log (v (uZ i)) = -Real.log (v (uMin i)) + -Real.log (v (c i:L)) := by
    rw [comparison,map_mul,Real.log_mul (hc i).ne' (hu i).ne']
    ring
  have hs : (∑ i, -Real.log (v (uZ i))) =
      (∑ i, -Real.log (v (uMin i))) + ∑ i, -Real.log (v (c i:L)) := by
    simp_rw [hrow,Finset.sum_add_distrib]
  have hmin := exact_row v m C hm hC uMin uMin_ne IMin minFrame
  have hres := exact_row v m C hm hC uZ uZ_ne IZ resFrame
  refine ⟨Finset.sum_nonneg (fun i _ => ?_),?_⟩
  · exact neg_nonneg.mpr (Real.log_nonpos (hc i).le (c i).property)
  · linarith only [hs,hmin.2,hres.2]

end SelectedBlowupSameMinor318

#print axioms SelectedBlowupSameMinor318.lift_integral_ratio
#print axioms SelectedBlowupSameMinor318.same_ordered_rows
#print axioms SelectedBlowupSameMinor318.exact_loss_shift
