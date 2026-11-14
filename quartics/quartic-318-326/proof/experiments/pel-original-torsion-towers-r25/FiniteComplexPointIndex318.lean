module
public import FiniteEtaleComplexSections318
public import FiniteComplexPointsScheme318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace FiniteComplexPointIndex318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FiniteComplexPointsScheme318
variable {X : Scheme} (π : X⟶Spec (CommRingCat.of ℂ))
  [IsFinite π] [Finite (Points π)]
local instance affine : IsAffine X := isAffine_of_isAffineHom π

/-- All actual closed points are all primes here, by genuine Jacobson
and finite closed-point topology, not by a reduced-support replacement. -/
lemma discrete : DiscreteTopology X := by
  letI : Finite (closedPoints X) := Finite.of_equiv (Points π) (pointEquivClosedPoint π)
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  exact JacobsonSpace.discreteTopology (Set.toFinite (closedPoints X))

@[expose] def pointEquiv : Points π ≃ X := by
  letI := discrete π
  exact (pointEquivClosedPoint π).trans
    { toFun := Subtype.val
      invFun := fun x => ⟨x,by rw [closedPoints_eq_univ]; trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The original affine global-section spectrum is identified with
ALL original complex scheme points through the canonical affine isomorphism. -/
@[expose] def primeEquiv : PrimeSpectrum Γ(X,⊤) ≃ Points π :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)).toEquiv.symm.trans
    (pointEquiv π).symm

local instance : Algebra ℂ Γ(X,⊤) := FiniteEtaleComplexSections318.algebra π
@[expose] def split [Etale π] : Γ(X,⊤) ≃ₐ[ℂ] (Points π→ℂ) :=
  (FiniteEtaleComplexSections318.split π).trans
    (AlgEquiv.piCongrLeft ℂ (fun _ : Points π => ℂ) (primeEquiv π))

/-- Actual scheme length over C equals the number of its complex points
only AFTER genuine finite étale splitting has removed infinitesimals. -/
lemma finrank [Etale π] : Module.finrank ℂ Γ(X,⊤)=Nat.card (Points π) := by
  letI : Fintype (Points π) := Fintype.ofFinite _
  rw [(split π).toLinearEquiv.finrank_eq,Module.finrank_pi]
  exact (Nat.card_eq_fintype_card).symm
end FiniteComplexPointIndex318
