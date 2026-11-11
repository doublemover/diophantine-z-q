module
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace NormalPrimitiveDerivativeConductor318
open Polynomial
attribute [local instance] Polynomial.algebra
variable {R K A L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Algebra R A]
  [Field L] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L]

/-- Every polynomial in the fraction field with integral coefficients
is the image of an actual polynomial over the SAME normal base. -/
lemma polynomial_descends (g : Polynomial K) (hg : ∀ i, IsIntegral R (g.coeff i)) :
    ∃ p : Polynomial R, p.map (algebraMap R K) = g := by
  classical
  choose c hc using fun i => IsIntegrallyClosed.algebraMap_eq_of_integral (hg i)
  refine ⟨∑ i ∈ g.support, Polynomial.monomial i (c i),?_⟩
  simpa only [Polynomial.map_sum,Polynomial.map_monomial,hc,←Polynomial.sum_def] using
    Polynomial.sum_monomial_eq g

/-- The literal derivative is a conductor from the WHOLE integral
algebra into its actual monogenic suborder. The generic presentation
has its full kernel and is surjective onto the SAME fraction field.
No arbitrary extra denominator is introduced. -/
theorem conductor (t : A) (Q : Polynomial R) (hm : Q.Monic)
    (hsurj : Function.Surjective
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L))
    (hker : RingHom.ker
      (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L).toRingHom =
      Ideal.span {Q.map (algebraMap R K)})
    (a : A) (ha : IsIntegral R a) :
    ∃ p : Polynomial R, Polynomial.aeval t Q.derivative * a = Polynomial.aeval t p := by
  let φ : Polynomial K →ₐ[R] L :=
    (Polynomial.aeval (algebraMap A L t) : Polynomial K →ₐ[K] L).restrictScalars R
  have hcoeff (i : ℕ) : IsIntegral R ((Q.map (algebraMap R K)).coeff i) := by
    rw [Polynomial.coeff_map]
    exact isIntegral_algebraMap
  have hy : IsIntegral R (algebraMap A L a) :=
    ha.map (IsScalarTower.toAlgHom R A L)
  obtain ⟨g,hg,hgi⟩ := exists_derivative_mul_eq_and_isIntegral_coeff
    (φ := φ) hsurj (hm.map (algebraMap R K)) hcoeff hker hy
  obtain ⟨p,hp⟩ := polynomial_descends g hgi
  have heval (q : Polynomial R) :
      φ (q.map (algebraMap R K)) = algebraMap A L (Polynomial.aeval t q) := by
    exact (Polynomial.map_aeval_eq_aeval_map
      (φ := algebraMap R K) (ψ := algebraMap A L)
      (by rw [←IsScalarTower.algebraMap_eq R K L,
        ←IsScalarTower.algebraMap_eq R A L]) q t).symm
  refine ⟨p,IsFractionRing.injective A L ?_⟩
  rw [map_mul,←heval,←heval]
  rw [Polynomial.derivative_map,←hp] at hg
  exact hg
end NormalPrimitiveDerivativeConductor318
