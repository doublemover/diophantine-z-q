module
public import SelectedOrdinateTorsor318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
open Polynomial
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open EvenContactEtale318 SelectedOrdinateTorsor318

namespace SelectedActualSignComplexLift318

variable (N : ℕ) (I : Ideal (D N))
local notation "R" => SelectedPrimitiveAffineSign318.R N
local notation "Q" => D N ⧸ I
variable (σ : Q →ₐ[R] Q) (hσ : σ.comp (q N I) = (q N I).comp (sign N))
local notation "F" => fixed N I σ
variable (hY : IsUnit (ybar N I))
local notation "d" => twistUnit N I σ hσ hY

/-- EVERY complex point of the actual sign quotient lifts to the
actual unsigned primitive affine algebra. The root adjoined is
the actual ordinate squared, rather than an unrelated double cover. -/
include hσ hY in
theorem lift_exists (f : F →+* ℂ) :
    ∃ g : Q →+* ℂ, ∀ a : F, g (a : Q) = f a := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (f (d:F)) (n := 2) (by decide)
  have he : (EvenContactEtale318.polynomial d).eval₂ f z = 0 := by
    simp [EvenContactEtale318.polynomial,hz]
  let e := rootIso N I σ hσ hY
  let b : RootRing d →+* ℂ := AdjoinRoot.lift f z he
  refine ⟨b.comp e.symm.toRingHom,?_⟩
  intro a
  change b (e.symm (algebraMap F Q a)) = f a
  rw [AlgEquiv.commutes,AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of he

end SelectedActualSignComplexLift318

#print axioms SelectedActualSignComplexLift318.lift_exists
