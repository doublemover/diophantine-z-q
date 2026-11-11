module
public import PolynomialWeightBounds318
public import WeightedMonicRootBound318
public import Mathlib.FieldTheory.Minpoly.Basic
public section
noncomputable section
namespace FiniteComplexEvaluationGrowth318
open Polynomial PolynomialWeightBounds318
variable {ι X A : Type*} [Fintype ι] [CommRing A] [Nontrivial A] [Algebra ℂ A]

/-- Every WHOLE algebra element in a finite polynomial normalization
has denominator-free polynomial growth on ALL complex fibers. The bound
comes from its genuine monic integral equation over the original base,
not from a localized coordinate formula. -/
theorem element (g : MvPolynomial ι ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (f : X → A →ₐ[ℂ] ℂ) (b : X → ι → ℂ)
    (hsquare : ∀ x r, f x (g r)=MvPolynomial.eval (b x) r) (a : A) :
    Bounded (fun x => 1+‖b x‖) (fun x => ‖f x a‖) := by
  let R := MvPolynomial ι ℂ
  letI : Algebra R A := g.toAlgebra
  letI : Module.Finite R A := hg
  let P := minpoly R a
  have hm : P.Monic := minpoly.monic (IsIntegral.of_finite R a)
  let W : X → ℝ := fun x => 1+‖b x‖
  have hW (x : X) : 1 ≤ W x := by dsimp [W]; positivity
  have hc (k : ℕ) : Bounded W (fun x => ‖MvPolynomial.eval (b x) (P.coeff k)‖) := by
    obtain ⟨C,hC,N,h⟩ := MvPolynomialEvaluationGrowth318.exists_growth (P.coeff k)
    exact ⟨C,hC,N,fun x => h (b x)⟩
  obtain ⟨C,hC,N,hcoeff⟩ := uniform hW (Finset.range P.natDegree) _ hc
  have hh : Bounded W (fun x => C*W x^N+1) :=
    add hW ⟨C,hC,N,fun _ => le_rfl⟩ (const 1)
  apply mono hh
  intro x
  let v : R →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) (b x)
  have hs : (algebraMap ℂ ℂ).comp v = (f x).toRingHom.comp (algebraMap R A) := by
    ext r
    exact (hsquare x r).symm
  have hz : (P.map v).IsRoot (f x a) := by
    have he := Polynomial.map_aeval_eq_aeval_map (φ := v) (ψ := (f x).toRingHom) hs P a
    rw [minpoly.aeval,map_zero] at he
    simpa only [Polynomial.aeval_def,algebraMap_self,Polynomial.eval₂_id] using he.symm
  have hcoeff' : ∀ k < (P.map v).natDegree, 1*‖(P.map v).coeff k‖ ≤ C*W x^N := by
    intro k hk
    rw [hm.natDegree_map v] at hk
    simpa only [one_mul,Polynomial.coeff_map] using hcoeff k (Finset.mem_range.mpr hk) x
  simpa only [one_mul] using WeightedMonicRootBound318.root_bound (P.map v) (hm.map v)
    1 (C*W x^N) zero_lt_one (mul_nonneg hC (pow_nonneg (zero_le_one.trans (hW x)) _))
    hcoeff' (f x a) hz
end FiniteComplexEvaluationGrowth318
