module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace SquareReflection318
set_option maxHeartbeats 600000

/-- Squares of integral elements in the actual fraction field descend to a
normal domain. This uses actual monic integrality, not a valuation model. -/
theorem fraction_square_iff {R K:Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (a:R) :
    IsSquare (algebraMap R K a) ↔ IsSquare a := by
  constructor
  · rintro ⟨y,hy⟩
    have hi:IsIntegral R y := by
      refine ⟨Polynomial.X^2-Polynomial.C a,
        Polynomial.monic_X_pow_sub_C _ (by decide : 2≠0),?_⟩
      change Polynomial.aeval y (Polynomial.X^2-Polynomial.C a)=0
      simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
      rw [pow_two,←hy,sub_self]
    obtain ⟨x,hx⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral hi
    refine ⟨x,(IsFractionRing.injective R K) ?_⟩
    rw [map_mul,hx,hy]
  · rintro ⟨x,rfl⟩
    exact ⟨algebraMap R K x,map_mul _ _ _⟩

/-- Exact square-class kernel of an actual quadratic algebra. The target
need not yet be a field; this statement helps establish that fact in towers. -/
theorem quadratic_square_iff {F:Type*} [Field F] [CharZero F] (a x:F) (ha:a≠0) :
    IsSquare (algebraMap F (QuadraticAlgebra F a 0) x) ↔ IsSquare x ∨ IsSquare (a*x) := by
  constructor
  · rintro ⟨y,hy⟩
    have hr:=congrArg QuadraticAlgebra.re hy
    have hi:=congrArg QuadraticAlgebra.im hy
    simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,mul_zero,zero_mul,add_zero] at hr hi
    have hp:y.re=0 ∨ y.im=0 := by
      have h:2*y.re*y.im=0 := by linear_combination -hi
      rcases mul_eq_zero.mp h with h|h
      · exact Or.inl ((mul_eq_zero.mp h).resolve_left (by norm_num))
      · exact Or.inr h
    rcases hp with hp|hp
    · right
      refine ⟨a*y.im,?_⟩
      rw [hp] at hr
      rw [hr]
      ring
    · left
      refine ⟨y.re,?_⟩
      simpa [hp] using hr
  · rintro (⟨y,hy⟩|⟨y,hy⟩)
    · refine ⟨algebraMap F (QuadraticAlgebra F a 0) y,?_⟩
      rw [←map_mul,←hy]
    · refine ⟨⟨0,y/a⟩,?_⟩
      apply QuadraticAlgebra.ext
      · change x=0*0+a*(y/a)*(y/a)
        field_simp [ha]
        linear_combination hy
      · simp
end SquareReflection318
