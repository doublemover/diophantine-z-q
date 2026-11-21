module
public import SelectedGeneralizedAffineInfinity318
public section
noncomputable section
open MvPolynomial Algebra SelectedGeneralizedAffineInfinity318

namespace SelectedGeneralizedProjectiveOverlap318

variable {R : Type*} [CommRing R]

/-- The dehomogenized Z=1 equation of the same denominator-free
generalized Weierstrass curve, over the same base. -/
@[expose] def finiteEquation (d : Rˣ) : MvPolynomial (Fin 2) R :=
  X 1^2+X 0*X 1-X 0^3+C (36*(↑d⁻¹ : R))*X 0+C (↑d⁻¹ : R)

@[expose] def finiteEquations (d : Rˣ) : Unit → MvPolynomial (Fin 2) R :=
  fun _ => finiteEquation d

abbrev FiniteChart (d : Rˣ) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (finiteEquations d))

@[expose] def x (d : Rˣ) : FiniteChart d := Ideal.Quotient.mk _ (X 0)
@[expose] def y (d : Rˣ) : FiniteChart d := Ideal.Quotient.mk _ (X 1)

@[expose] def finiteValue {D : Type*} [CommRing D] [Algebra R D] (d : Rˣ)
    (x y : D) : D :=
  y^2+x*y-x^3+algebraMap R D (36*(↑d⁻¹ : R))*x+algebraMap R D (↑d⁻¹ : R)

@[expose] def infinityValue {D : Type*} [CommRing D] [Algebra R D] (d : Rˣ)
    (t z : D) : D :=
  z+t*z-t^3+algebraMap R D (36*(↑d⁻¹ : R))*t*z^2+algebraMap R D (↑d⁻¹ : R)*z^3

variable {D : Type*} [CommRing D] [Algebra R D]

theorem eval_finiteEquation (d : Rˣ) (a b : D) :
    MvPolynomial.aeval ![a,b] (finiteEquation d) = finiteValue d a b := by
  simp only [finiteEquation,finiteValue,map_pow,map_mul,map_add,map_sub,
    MvPolynomial.aeval_C,MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem eval_infinityEquation (d : Rˣ) (a b : D) :
    MvPolynomial.aeval ![a,b] (equation d) = infinityValue d a b := by
  simp only [equation,infinityValue,map_pow,map_mul,map_add,map_sub,
    MvPolynomial.aeval_C,MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem finite_dehomogenizes (d : Rˣ) (a b : D) :
    ((SelectedGeneralizedJCurve318.curve d).baseChange D).toProjective.Equation ![a,b,1] ↔
      finiteValue d a b = 0 := by
  rw [WeierstrassCurve.Projective.equation_iff]
  change b^2*1+(algebraMap R D 1)*a*b*1+(algebraMap R D 0)*b*1^2 -
    (a^3+(algebraMap R D 0)*a^2*1+(algebraMap R D (-36*(↑d⁻¹ : R)))*a*1^2+
      (algebraMap R D (-(↑d⁻¹ : R)))*1^3) = 0 ↔ _
  simp only [map_neg,map_mul,map_ofNat,map_one,map_zero,zero_mul,mul_one,one_mul,one_pow,add_zero,
    finiteValue]
  constructor <;> intro h <;> (convert h using 1 <;> ring)

/-- Actual transition to Y=1, retaining all mixed terms over any ring. -/
theorem finite_to_infinity (d : Rˣ) (a b k : D) (h : b*k = 1) :
    infinityValue d (a*k) k = k^3*finiteValue d a b := by
  unfold infinityValue finiteValue
  calc
    _ = k^3*(b^2+a*b-a^3+algebraMap R D (36*(↑d⁻¹ : R))*a+
          algebraMap R D (↑d⁻¹ : R)) + k*(1-(b*k)^2) + a*k^2*(1-b*k) := by ring
    _ = _ := by rw [h]; ring

/-- Actual transition to Z=1, before any restriction to generic fields. -/
theorem infinity_to_finite (d : Rˣ) (a b k : D) (h : b*k = 1) :
    finiteValue d (a*k) k = k^3*infinityValue d a b := by
  unfold infinityValue finiteValue
  calc
    _ = k^3*(b+a*b-a^3+algebraMap R D (36*(↑d⁻¹ : R))*a*b^2+
          algebraMap R D (↑d⁻¹ : R)*b^3) + (1-b*k)*(k^2+a*k^2+
          algebraMap R D (36*(↑d⁻¹ : R))*a*k*(b*k+1)+
          algebraMap R D (↑d⁻¹ : R)*((b*k)^2+b*k+1)) := by ring
    _ = _ := by rw [h]; ring

@[expose] def coordinateEval (a b : D) : MvPolynomial (Fin 2) R →ₐ[R] D :=
  MvPolynomial.aeval ![a,b]

private theorem finiteLift_vanishes (d : Rˣ) (a b : D) (h : finiteValue d a b = 0)
    (f : MvPolynomial (Fin 2) R) (hf : f ∈ Ideal.span (Set.range (finiteEquations d))) :
    coordinateEval a b f = 0 := by
  let ev : MvPolynomial (Fin 2) R →ₐ[R] D := coordinateEval a b
  have hi : Ideal.span (Set.range (finiteEquations d)) ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.2
    rintro _ ⟨_,rfl⟩
    exact (eval_finiteEquation d a b).trans h
  exact RingHom.mem_ker.mp (hi hf)

private theorem infinityLift_vanishes (d : Rˣ) (a b : D) (h : infinityValue d a b = 0)
    (f : MvPolynomial (Fin 2) R) (hf : f ∈ Ideal.span (Set.range (equations d))) :
    coordinateEval a b f = 0 := by
  let ev : MvPolynomial (Fin 2) R →ₐ[R] D := coordinateEval a b
  have hi : Ideal.span (Set.range (equations d)) ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.2
    rintro _ ⟨_,rfl⟩
    exact (eval_infinityEquation d a b).trans h
  exact RingHom.mem_ker.mp (hi hf)

@[expose] def finiteLift (d : Rˣ) (a b : D) (h : finiteValue d a b = 0) :
    FiniteChart d →ₐ[R] D :=
  Ideal.Quotient.liftₐ _ (coordinateEval a b) (by exact finiteLift_vanishes d a b h)

@[expose] def infinityLift (d : Rˣ) (a b : D) (h : infinityValue d a b = 0) :
    Chart d →ₐ[R] D :=
  Ideal.Quotient.liftₐ _ (coordinateEval a b) (by exact infinityLift_vanishes d a b h)

private theorem finiteLift_mk (d : Rˣ) (a b : D) (h : finiteValue d a b = 0) (f : MvPolynomial (Fin 2) R) :
    finiteLift d a b h (Ideal.Quotient.mk _ f) = coordinateEval a b f := by
  have he := Ideal.Quotient.liftₐ_comp (Ideal.span (Set.range (finiteEquations d)))
    (coordinateEval (R := R) a b) (finiteLift_vanishes d a b h)
  have hf := DFunLike.congr_fun he f
  change finiteLift d a b h (Ideal.Quotient.mk _ f) = coordinateEval a b f at hf
  exact hf

private theorem infinityLift_mk (d : Rˣ) (a b : D) (h : infinityValue d a b = 0) (f : MvPolynomial (Fin 2) R) :
    infinityLift d a b h (Ideal.Quotient.mk _ f) = coordinateEval a b f := by
  have he := Ideal.Quotient.liftₐ_comp (Ideal.span (Set.range (equations d)))
    (coordinateEval (R := R) a b) (infinityLift_vanishes d a b h)
  have hf := DFunLike.congr_fun he f
  change infinityLift d a b h (Ideal.Quotient.mk _ f) = coordinateEval a b f at hf
  exact hf

@[simp] theorem finiteLift_x (d : Rˣ) (a b : D) (h) : finiteLift d a b h (x d) = a := by
  rw [x,finiteLift_mk]
  simp only [coordinateEval,MvPolynomial.aeval_X,Matrix.cons_val_zero]
@[simp] theorem finiteLift_y (d : Rˣ) (a b : D) (h) : finiteLift d a b h (y d) = b := by
  rw [y,finiteLift_mk]
  simp only [coordinateEval,MvPolynomial.aeval_X,Matrix.cons_val_one]
@[simp] theorem infinityLift_t (d : Rˣ) (a b : D) (h) : infinityLift d a b h (parameter d) = a := by
  rw [parameter,infinityLift_mk]
  simp only [coordinateEval,MvPolynomial.aeval_X,Matrix.cons_val_zero]
@[simp] theorem infinityLift_z (d : Rˣ) (a b : D) (h) : infinityLift d a b h (ordinate d) = b := by
  rw [ordinate,infinityLift_mk]
  simp only [coordinateEval,MvPolynomial.aeval_X,Matrix.cons_val_one]

theorem finite_ext (d : Rˣ) {f g : FiniteChart d →ₐ[R] D}
    (hx : f (x d) = g (x d)) (hy : f (y d) = g (y d)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy

theorem infinity_ext (d : Rˣ) {f g : Chart d →ₐ[R] D}
    (ht : f (parameter d) = g (parameter d)) (hz : f (ordinate d) = g (ordinate d)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact ht
  · exact hz

end SelectedGeneralizedProjectiveOverlap318

#print axioms SelectedGeneralizedProjectiveOverlap318.finite_dehomogenizes
#print axioms SelectedGeneralizedProjectiveOverlap318.finite_to_infinity
#print axioms SelectedGeneralizedProjectiveOverlap318.infinity_to_finite
