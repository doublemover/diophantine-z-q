module
public import JacobianLocalSmooth318
public import OpenJModel318
public section
noncomputable section
namespace ShortAffineJacobian318
open MvPolynomial Algebra
set_option maxHeartbeats 0
variable {R : Type*} [CommRing R]

@[expose] def equation (A B : R) : MvPolynomial (Fin 2) R :=
  X 1^2-X 0^3-C A*X 0-C B
@[expose] def equations (A B : R) : Unit → MvPolynomial (Fin 2) R := fun _ => equation A B
abbrev Ring (A B : R) := MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (equations A B))
@[expose] def x (A B : R) : Ring A B := Ideal.Quotient.mk _ (X 0)
@[expose] def y (A B : R) : Ring A B := Ideal.Quotient.mk _ (X 1)

lemma mk_C (A B r : R) :
    Ideal.Quotient.mk (Ideal.span (Set.range (equations A B))) (C r)=algebraMap R (Ring A B) r := rfl

lemma relation (A B : R) : y A B^2-x A B^3-algebraMap R (Ring A B) A*x A B-
    algebraMap R (Ring A B) B=0 := by
  have hh : Ideal.Quotient.mk (Ideal.span (Set.range (equations A B))) (equation A B)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(),rfl⟩)
  simpa only [equation,map_sub,map_pow,map_mul,mk_C,x,y] using hh

@[expose] def presentation (A B : R) (i : Fin 2) :
    PreSubmersivePresentation R (Ring A B) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations A B) (fun _ => i)
    (fun _ _ _ => Subsingleton.elim _ _)

lemma jacobian_formula (A B : R) (i : Fin 2) :
    (presentation A B i).jacobian=Ideal.Quotient.mk _ (pderiv i (equation A B)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

lemma pderiv_x (A B : R) : pderiv 0 (equation A B)= -3*X 0^2-C A := by
  simp [equation]
lemma pderiv_y (A B : R) : pderiv 1 (equation A B)=2*X 1 := by
  simp [equation]

lemma jacobian_x (A B : R) :
    (presentation A B 0).jacobian= -3*x A B^2-algebraMap R (Ring A B) A := by
  rw [jacobian_formula,pderiv_x]
  simp only [map_sub,map_neg,map_mul,map_pow,map_ofNat,mk_C,x]
lemma jacobian_y (A B : R) : (presentation A B 1).jacobian=2*y A B := by
  rw [jacobian_formula,pderiv_y]
  simp only [map_mul,map_ofNat,y]

/-- Explicit discriminant Bezout identity in the actual affine coordinate ring. -/
theorem discriminant_identity (A B : R) :
    algebraMap R (Ring A B) (-16*(4*A^3+27*B^2))=
      16*(6*algebraMap R (Ring A B) A*x A B^2-9*algebraMap R (Ring A B) B*x A B+
        4*(algebraMap R (Ring A B) A)^2)*(presentation A B 0).jacobian-
      8*(27*algebraMap R (Ring A B) B-18*algebraMap R (Ring A B) A*x A B)*y A B*
        (presentation A B 1).jacobian := by
  rw [jacobian_x,jacobian_y]
  simp only [map_neg,map_mul,map_add,map_pow,map_ofNat]
  linear_combination 16*(27*algebraMap R (Ring A B) B-18*algebraMap R (Ring A B) A*x A B)*relation A B

/-- The two actual Jacobian minors cover the entire affine scheme. -/
theorem jacobian_span (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    Ideal.span (Set.range (fun i : Fin 2 => (presentation A B i).jacobian))=⊤ := by
  let I := Ideal.span (Set.range (fun i : Fin 2 => (presentation A B i).jacobian))
  apply I.eq_top_of_isUnit_mem (x := algebraMap R (Ring A B) (-16*(4*A^3+27*B^2)))
  · rw [discriminant_identity]
    apply I.sub_mem
    · exact I.mul_mem_left _ (Ideal.subset_span ⟨0,rfl⟩)
    · exact I.mul_mem_left _ (Ideal.subset_span ⟨1,rfl⟩)
  · exact hD.map (algebraMap R (Ring A B))

/-- The literal affine short-Weierstrass coordinate algebra is genuinely smooth
when its actual discriminant is a unit. -/
theorem smooth (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2))) : Algebra.Smooth R (Ring A B) := by
  rw [← RingHom.smooth_algebraMap,RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (fun i : Fin 2 => (presentation A B i).jacobian),jacobian_span A B hD,?_⟩
  rintro t ⟨i,rfl⟩
  rw [← IsScalarTower.algebraMap_eq,RingHom.isStandardSmooth_algebraMap]
  exact JacobianLocalSmooth318.localization_jacobian (presentation A B i)

end ShortAffineJacobian318
