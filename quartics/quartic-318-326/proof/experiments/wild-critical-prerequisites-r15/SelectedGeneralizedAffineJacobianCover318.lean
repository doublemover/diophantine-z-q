module
public import SelectedGeneralizedProjectiveOverlap318
import Mathlib.Tactic.LinearCombination
public section
noncomputable section
open MvPolynomial Algebra
open SelectedGeneralizedProjectiveOverlap318

namespace SelectedGeneralizedAffineJacobianCover318

variable {R : Type*} [CommRing R]

theorem finite_relation (d : Rˣ) : finiteValue d (x d) (y d) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (finiteEquations d))) (finiteEquation d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(),rfl⟩)
  simp only [finiteEquation,map_add,map_sub,map_mul,map_pow] at h
  let q : MvPolynomial (Fin 2) R →+* FiniteChart d := Ideal.Quotient.mk _
  have hCoeff : q (C (36 : R)) * q (C (↑d⁻¹ : R)) =
      algebraMap R (FiniteChart d) (36*(↑d⁻¹ : R)) := by
    change q (C (36 : R)) * q (C (↑d⁻¹ : R)) = q (C (36*(↑d⁻¹ : R)))
    simp only [map_mul]
  change q (X 1)^2 + q (X 0)*q (X 1) - q (X 0)^3 +
    q (C (36 : R))*q (C (↑d⁻¹ : R))*q (X 0) + q (C (↑d⁻¹ : R)) = 0 at h
  rw [hCoeff] at h
  change finiteValue d (x d) (y d) = 0 at h
  exact h

@[expose] def gradientX (d : Rˣ) : FiniteChart d :=
  y d-3*(x d)^2+algebraMap R (FiniteChart d) (36*(↑d⁻¹ : R))
@[expose] def gradientY (d : Rˣ) : FiniteChart d := 2*y d+x d

private theorem nonzero_of_unit_map {A B : Type*} [CommRing A] [CommRing B]
    [Nontrivial B] (f : A →+* B) {a : A} (h : IsUnit a) : f a ≠ 0 :=
  (h.map f).ne_zero

/-- The derivative opens cover the literal generalized affine curve,
including residue characteristics 2 and 3. This is an ideal equality
over the actual coordinate algebra, not just a field point test. -/
theorem gradients_span (J : R) (d : Rˣ) (hd : (d:R) = J-1728) (hJ : IsUnit J) :
    Ideal.span ({gradientX d,gradientY d} : Set (FiniteChart d)) = ⊤ := by
  let I : Ideal (FiniteChart d) := Ideal.span {gradientX d,gradientY d}
  change I = ⊤
  by_contra hn
  let Q := FiniteChart d ⧸ I
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 hn
  let q := Ideal.Quotient.mkₐ R I
  let W := (SelectedGeneralizedJCurve318.curve d).baseChange Q
  have hd' : W.Δ ≠ 0 := by
    have h : IsUnit (SelectedGeneralizedJCurve318.curve d).Δ :=
      (SelectedGeneralizedJCurve318.isElliptic J d hd hJ).isUnit
    change ((SelectedGeneralizedJCurve318.curve d).map (algebraMap R Q)).Δ ≠ 0
    rw [WeierstrassCurve.map_Δ]
    exact nonzero_of_unit_map (A := R) (B := Q) (algebraMap R Q) h
  have heqF : finiteValue d (q (x d)) (q (y d)) = 0 := by
    have h := congrArg q (finite_relation d)
    simpa only [finiteValue,map_add,map_sub,map_mul,map_pow,map_zero,q.commutes] using h
  have heq : W.toAffine.Equation (q (x d)) (q (y d)) := by
    apply (WeierstrassCurve.Projective.equation_some (W' := W.toProjective) _ _).1
    exact (finite_dehomogenizes d _ _).2 heqF
  have hs := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (W := W.toAffine) hd').1 heq
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hs
  have hX : q (gradientX d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp : gradientX d ∈ {gradientX d,gradientY d}))
  have hY : q (gradientY d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp : gradientY d ∈ {gradientX d,gradientY d}))
  have hX' : W.a₁*q (y d) - (3*(q (x d))^2 + 2*W.a₂*q (x d)+W.a₄) = 0 := by
    change algebraMap R Q 1*q (y d) -
      (3*(q (x d))^2+2*algebraMap R Q 0*q (x d)+algebraMap R Q (-36*(↑d⁻¹ : R))) = 0
    simp only [gradientX,map_add,map_sub,map_mul,map_pow,map_ofNat,q.commutes] at hX
    simp only [map_one,map_zero,one_mul,mul_zero,zero_mul,add_zero,map_mul,map_neg,map_ofNat]
    linear_combination hX
  have hY' : 2*q (y d)+W.a₁*q (x d)+W.a₃ = 0 := by
    change 2*q (y d)+algebraMap R Q 1*q (x d)+algebraMap R Q 0=0
    simp only [map_one,map_zero,add_zero]
    have h : 2 * q (y d) + q (x d) = (0 : Q) := by
      simpa only [gradientY,map_add,map_mul,map_ofNat] using hY
    exact (congrArg (fun t : Q => 2 * q (y d) + t) (one_mul (q (x d)))).trans h
  exact hs.2.elim (fun h => h hX') (fun h => h hY')

end SelectedGeneralizedAffineJacobianCover318

#print axioms SelectedGeneralizedAffineJacobianCover318.gradients_span
