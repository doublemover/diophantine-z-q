module
public import SelectedOrdinateTorsor318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open EvenContactEtale318 SelectedOrdinateTorsor318

namespace SelectedActualSignComplexLift318

attribute [local instance 2000] fixedRing fixedAlgebra

private theorem lift_root_map {S Q : Type*} [CommRing S] [CommRing Q] [Algebra S Q]
    (d : Sˣ) (e : RootRing d ≃ₐ[S] Q) (f : S →+* ℂ) :
    ∃ g : Q →+* ℂ, ∀ a : S, g (algebraMap S Q a) = f a := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (f (d:S)) (n := 2) (by decide)
  have he : (EvenContactEtale318.polynomial d).eval₂ f z = 0 := by
    simp [EvenContactEtale318.polynomial,hz]
  let b : RootRing d →+* ℂ := AdjoinRoot.lift f z he
  refine ⟨b.comp e.symm.toRingHom,?_⟩
  intro a
  change b (e.symm (algebraMap S Q a)) = f a
  rw [e.symm.commutes,AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of he

/-- EVERY complex point of the actual sign quotient lifts to the
actual unsigned primitive affine algebra. The root adjoined is
the actual ordinate squared, rather than an unrelated double cover. -/
theorem lift_exists (N : ℕ) (I : Ideal (D N))
    (σ : (D N ⧸ I) →ₐ[SelectedPrimitiveAffineSign318.R N] (D N ⧸ I))
    (hσ : σ.comp (q N I) = (q N I).comp (sign N))
    (hY : IsUnit (ybar N I)) (f : ↥(fixed N I σ) →+* ℂ) :
    ∃ g : (D N ⧸ I) →+* ℂ, ∀ a : ↥(fixed N I σ), g (a : D N ⧸ I) = f a := by
  exact lift_root_map (S := ↥(fixed N I σ)) (Q := D N ⧸ I)
    (twistUnit N I σ hσ hY) (rootIso N I σ hσ hY) f

end SelectedActualSignComplexLift318

#print axioms SelectedActualSignComplexLift318.lift_exists
