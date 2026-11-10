module
public import UnitScaledQuadraticOrder318
public section
noncomputable section
namespace IntegralWholeReciprocalOrders318
open Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The full finite three-root presentation in the original root y0,
not just the unbranched t-coordinate open. -/
@[expose] def finiteCoefficient (j : Fin 3) : R[X] :=
  C (c j.succ : R)*(C (↑(c 0)⁻¹:R)*X^2-C (IntegralInfinityChart318.contact R j))
abbrev FiniteOrder := ThreeRootOrder318.Order (finiteCoefficient R c)
/-- Whole reciprocal order BEFORE inverting the other-root product. -/
abbrev InfinityOrder := ThreeRootOrder318.Order (IntegralInfinityChart318.coefficient R c)

instance finite_finite : Module.Finite R[X] (FiniteOrder R c) :=
  (ThreeRootOrder318.finite_free _).1
instance finite_free : Module.Free R[X] (FiniteOrder R c) :=
  (ThreeRootOrder318.finite_free _).2
instance infinity_finite : Module.Finite R[X] (InfinityOrder R c) :=
  (ThreeRootOrder318.finite_free _).1
instance infinity_free : Module.Free R[X] (InfinityOrder R c) :=
  (ThreeRootOrder318.finite_free _).2

theorem finite_rank [Nontrivial R] : Module.finrank R[X] (FiniteOrder R c)=8 :=
  ThreeRootOrder318.rank_eight _
theorem infinity_rank [Nontrivial R] : Module.finrank R[X] (InfinityOrder R c)=8 :=
  ThreeRootOrder318.rank_eight _

/-- The existing infinity chart is the literal base localization of this
whole order, not an unrelated finite-free algebra of the same rank. -/
@[expose] def infinityLocalization :
    IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c ≃ₐ[
      IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c :=
  ThreeRootOrder318.baseChange _ _

/-- Over every prime of the whole reciprocal order, either the reciprocal
coordinate or the original denominator is invertible. This is all-prime
coverage, including all omitted branch points. -/
theorem infinity_opens_cover (p : PrimeSpectrum (InfinityOrder R c)) :
    p ∈ PrimeSpectrum.basicOpen (algebraMap R[X] (InfinityOrder R c) X) ∨
    p ∈ PrimeSpectrum.basicOpen
      (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c)) := by
  by_cases hx : algebraMap R[X] (InfinityOrder R c) X ∈ p.asIdeal
  · right
    intro hd
    have hv : ∀ q : R[X],
        algebraMap R[X] (InfinityOrder R c) q -
          algebraMap R (InfinityOrder R c) (Polynomial.eval 0 q) ∈ p.asIdeal := by
      intro q
      obtain ⟨r,hr⟩ := Polynomial.X_dvd_iff.mpr (show (q-C (Polynomial.eval 0 q)).coeff 0=0 by simp)
      have he := congrArg (algebraMap R[X] (InfinityOrder R c)) hr
      rw [map_sub,map_mul] at he
      change algebraMap R[X] (InfinityOrder R c) q -
        algebraMap R[X] (InfinityOrder R c) (C (Polynomial.eval 0 q)) ∈ p.asIdeal
      rw [he]
      exact p.asIdeal.mul_mem_right _ hx
    have hc : algebraMap R (InfinityOrder R c)
        (Polynomial.eval 0 (IntegralInfinityChart318.denominator R c)) ∈ p.asIdeal := by
      have hh := p.asIdeal.sub_mem hd (hv (IntegralInfinityChart318.denominator R c))
      simpa only [sub_sub_cancel] using hh
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hc
      ((IntegralInfinityChart318.denominator_at_zero_unit R c).map
        (algebraMap R (InfinityOrder R c))))
  · exact Or.inl hx
end IntegralWholeReciprocalOrders318
