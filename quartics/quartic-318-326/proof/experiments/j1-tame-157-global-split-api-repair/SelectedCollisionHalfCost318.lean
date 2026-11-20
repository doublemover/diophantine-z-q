module
public import SelectedJOneExactMinorLoss318
public section
noncomputable section
open NumberField
open SelectedJOneExactMinorLoss318
open scoped BigOperators

namespace SelectedCollisionHalfCost318
variable {L : Type*} [Field L] [NumberField L]
variable (v : FinitePlace L)

/-- Unit quadratic j-1728 contact and a unit times the SAME parameter in
the differential imply the half-cost, over the actual finite place. -/
theorem contact_half {x u c d : L} (hc : v c = 1) (hd : v d = 1)
    (contact : -(1727:L) = c*x^2) (differential : u = d*x) :
    -Real.log (v u) = -(Real.log (v (1727:L)) / 2) := by
  have hV : v (1727:L) = (v x)^2 := by
    calc
      _ = v (-(1727:L)) := (map_neg_eq_map v _).symm
      _ = _ := by rw [contact,map_mul,map_pow,hc,one_mul]
  have hU : v u = v x := by rw [differential,map_mul,hd,one_mul]
  rw [hU,hV,Real.log_pow]
  ring

theorem contact_157 {x u c d : L} (hc : v c = 1) (hd : v d = 1)
    (h11 : v (11:L) = 1)
    (contact : -(1727:L) = c*x^2) (differential : u = d*x) :
    -Real.log (v u) = (-Real.log (v (157:L))) / 2 := by
  have h1727 : v (1727:L) = v (157:L) := by
    rw [show (1727:L) = (11:L)*157 by norm_num,map_mul,h11,one_mul]
  rw [contact_half v hc hd contact differential,h1727]
  ring

variable {g : ℕ}
variable (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
variable (u x c d : Fin g → L) (hu : ∀ i, u i ≠ 0)
variable (I : Matrix (Fin g) (Fin g) (integralAt v))
variable (frames : baseMatrix v I = Matrix.diagonal u * m * C)

include hm hC hu frames in
/-- Tame off-level 157 collision: retain the SAME determinant loss, in
addition to the exact half contribution of the literal 1727 collision. -/
theorem exact_157 (h11 : v (11:L) = 1)
    (hc : ∀ i, v (c i) = 1) (hd : ∀ i, v (d i) = 1)
    (contact : ∀ i, -(1727:L) = c i*(x i)^2)
    (differential : ∀ i, u i = d i*x i) :
    0 ≤ -Real.log (v (baseMatrix v I).det) ∧
      -Real.log (v ((m.det*C.det)⁻¹)) =
        ((g:ℝ)/2)*(-Real.log (v (157:L))) - (-Real.log (v (baseMatrix v I).det)) := by
  have h := exact_row v m C hm hC u hu I frames
  refine ⟨h.1,?_⟩
  rw [h.2]
  simp_rw [fun i => contact_157 v (hc i) (hd i) h11 (contact i) (differential i)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end SelectedCollisionHalfCost318

#print axioms SelectedCollisionHalfCost318.contact_157
#print axioms SelectedCollisionHalfCost318.exact_157
