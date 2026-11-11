module
public import FiniteNormalAlgebraProjection318
public section
noncomputable section
namespace FiniteNormalAlgebraProjectionProper318
open Set Polynomial
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (A : Type) [CommRing A] [IsDomain A]
  [Algebra (MvPolynomial κ ℂ) A] [Algebra ℂ A]
  [IsScalarTower ℂ (MvPolynomial κ ℂ) A]
  [Module.Finite (MvPolynomial κ ℂ) A]

/-- Actual whole finite coordinate equations make the full projection
proper. This does not restrict to a simple-root or denominator open. -/
theorem projection_proper
    (a : ι → A) (S : Set (ι → ℂ)) (hS : IsClosed S)
    (e : S → (A →ₐ[ℂ] ℂ))
    (he : ∀ w : S, ∀ i, e w (a i) = w.val i)
    (π : (ι → ℂ) → (κ → ℂ)) (hπ : Continuous π)
    (hb : ∀ w : S, ∀ r : MvPolynomial κ ℂ,
      e w (algebraMap (MvPolynomial κ ℂ) A r) = MvPolynomial.eval (π w.val) r) :
    IsProperMap (fun w : S => π w.val) := by
  let R := MvPolynomial κ ℂ
  apply IntegralCoordinateProperMap318.proper_of_monic_coordinates S hS π hπ
    (fun i => minpoly R (a i))
    (fun i => minpoly.monic (IsIntegral.of_finite R (a i)))
  intro w hw i
  let q : S := ⟨w,hw⟩
  have h := congrArg (e q) (minpoly.aeval R (a i))
  change e q ((minpoly R (a i)).eval₂ (algebraMap R A) (a i)) = e q 0 at h
  have hbase : (e q).toRingHom.comp (algebraMap R A) = MvPolynomial.eval (π w) :=
    RingHom.ext (hb q)
  rw [Polynomial.hom_eval₂,hbase,map_zero,he] at h
  simpa only [Polynomial.IsRoot,Polynomial.eval_map] using h
end FiniteNormalAlgebraProjectionProper318
