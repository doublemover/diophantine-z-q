module
public import OriginalUniformSparseSmoothChart318
public import JacobianLocalSmooth318

/-! A represented affine chart of the literal sparse genus-two family.
Its two actual partials generate the unit ideal on the nonexception
open, so the actual chart algebra is smooth. Its global proper
completion and relative Jacobian are deliberately separate. -/
public section
noncomputable section

namespace OriginalUniformSparseAffineModel318

open MvPolynomial Algebra
open OriginalUniformSparseSmoothChart318 (eqVal derVal delta u v bezout)

variable {R : Type*} [CommRing R]

@[expose] def eq (s t : R) : MvPolynomial (Fin 2) R :=
  X 1^2 - eqVal (C s) (C t) (X 0)

@[expose] def equations (s t : R) : Unit → MvPolynomial (Fin 2) R :=
  fun _ => eq s t

abbrev Ring (s t : R) := MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (equations s t))

@[expose] def x (s t : R) : Ring s t := Ideal.Quotient.mk _ (X 0)
@[expose] def y (s t : R) : Ring s t := Ideal.Quotient.mk _ (X 1)
@[expose] def base (s t : R) (r : R) : Ring s t := algebraMap R (Ring s t) r

private theorem mk_C (s t r : R) :
    Ideal.Quotient.mk (Ideal.span (Set.range (equations s t))) (C r) = base s t r := rfl

theorem relation (s t : R) :
    y s t^2 = eqVal (base s t s) (base s t t) (x s t) := by
  have hh : Ideal.Quotient.mk (Ideal.span (Set.range (equations s t))) (eq s t)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(),rfl⟩)
  apply sub_eq_zero.mp
  simpa only [eq,eqVal,map_sub,map_pow,map_mul,map_add,map_neg,map_ofNat,mk_C,x,y] using hh

@[expose] def presentation (s t : R) (i : Fin 2) :
    PreSubmersivePresentation R (Ring s t) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations s t) (fun _ => i)
    (fun _ _ _ => Subsingleton.elim _ _)

theorem jacobian_formula (s t : R) (i : Fin 2) :
    (presentation s t i).jacobian = Ideal.Quotient.mk _ (pderiv i (eq s t)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

private theorem pderiv_literal (i : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (OfNat.ofNat n : MvPolynomial (Fin 2) R)=0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial (Fin 2) R) n, pderiv_C]

theorem pderiv_x (s t : R) : pderiv 0 (eq s t) = -derVal (C s) (C t) (X 0) := by
  simp [eq,eqVal,derVal,pderiv_literal (R:=R) 0 2,pderiv_literal (R:=R) 0 5,
    pderiv_literal (R:=R) 0 10]
  ring

theorem pderiv_y (s t : R) : pderiv 1 (eq s t) = 2*X 1 := by
  simp [eq,eqVal,pderiv_literal (R:=R) 1 2,pderiv_literal (R:=R) 1 5,
    pderiv_literal (R:=R) 1 10]

theorem jacobian_x (s t : R) :
    (presentation s t 0).jacobian = -derVal (base s t s) (base s t t) (x s t) := by
  rw [jacobian_formula,pderiv_x]
  simp only [derVal,map_neg,map_sub,map_add,map_mul,map_pow,map_ofNat,mk_C,x]

theorem jacobian_y (s t : R) : (presentation s t 1).jacobian = 2*y s t := by
  rw [jacobian_formula,pderiv_y]
  simp only [map_mul,map_ofNat,y]

theorem jacobian_combination (s t : R) :
    base s t (2*delta s t) =
      u (base s t s) (base s t t) (x s t) * y s t * (presentation s t 1).jacobian -
      2*v (base s t s) (base s t t) (x s t) * (presentation s t 0).jacobian := by
  have b := bezout (base s t s) (base s t t) (x s t)
  rw [← relation s t] at b
  rw [jacobian_x,jacobian_y]
  have h : base s t (2*delta s t) = 2*delta (base s t s) (base s t t) := by
    unfold base delta OriginalUniformSparseSmoothChart318.collision
    simp only [map_mul,map_pow,map_add,map_sub,map_neg,map_ofNat]
  rw [h, ← b]
  ring

theorem jacobian_span (s t : R) (h2 : IsUnit (2:R)) (hd : IsUnit (delta s t)) :
    Ideal.span (Set.range (fun i : Fin 2 => (presentation s t i).jacobian)) = ⊤ := by
  let I := Ideal.span (Set.range (fun i : Fin 2 => (presentation s t i).jacobian))
  apply I.eq_top_of_isUnit_mem (x := base s t (2*delta s t))
  · rw [jacobian_combination]
    apply I.sub_mem
    · exact I.mul_mem_left _ (Ideal.subset_span ⟨1,rfl⟩)
    · exact I.mul_mem_left _ (Ideal.subset_span ⟨0,rfl⟩)
  · exact (h2.mul hd).map (algebraMap R (Ring s t))

/-- Smoothness of the actual defining algebra, not a condition on a
residue scalar. Units are pulled back on the chosen nonexception open. -/
theorem smooth (s t : R) (h2 : IsUnit (2:R)) (hd : IsUnit (delta s t)) :
    Algebra.Smooth R (Ring s t) := by
  rw [← RingHom.smooth_algebraMap,RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (fun i : Fin 2 => (presentation s t i).jacobian),jacobian_span s t h2 hd,?_⟩
  rintro j ⟨i,rfl⟩
  rw [← IsScalarTower.algebraMap_eq,RingHom.isStandardSmooth_algebraMap]
  exact JacobianLocalSmooth318.localization_jacobian (presentation s t i)

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- The same literal smooth affine model in each eligible characteristic-zero
specialization, using the actual invariant computation rather than a supplied
third-party formal smoothness proof. -/
theorem smooth_of_igusa (s t : K) (hi : OriginalUniformSparseIgusa318.i10 s t ≠ 0) :
    Algebra.Smooth K (Ring s t) :=
  smooth s t (isUnit_iff_ne_zero.mpr (by norm_num))
    (OriginalUniformSparseSmoothChart318.unit_of_igusa s t hi)
end Field

end OriginalUniformSparseAffineModel318

#print axioms OriginalUniformSparseAffineModel318.smooth
#print axioms OriginalUniformSparseAffineModel318.smooth_of_igusa
