module
public import AffineTripleCoordinateLaws318
public import AffineOverlapDiagonal318
public import AffineCoalgebraModule318
public section
noncomputable section
namespace AffineOverlapCoassociativity318
open CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open AffineCechRings318 AffineTripleCoactionCoordinates318 AffineTripleOverlapMaps318
open AffineTripleCoordinateLaws318
open scoped ChangeOfRings
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (N : ModuleCat.{u} S)

/-- The genuine triple-overlap cocycle implies coassociativity of the
existing candidate coaction. The proof evaluates the actual cocycle at a
unit tensor and uses the canonical full triple-coordinate comparison. -/
theorem coassoc_of_cocycle (τ : first R S N ⟶ second R S N)
    (hτ : Cocycle R S N τ) :
    homEquiv R S N τ ≫ (comonad R S).toFunctor.map (homEquiv R S N τ) =
      homEquiv R S N τ ≫ (comonad R S).δ.app N := by
  ext n
  have hn := congrArg (fun k : vertexModule R S N (vertex1 R S) ⟶
      vertexModule R S N (vertex3 R S) =>
      (coordinates R S N).hom (k ((1 : triple R S) ⊗ₜ[S, (vertex1 R S).hom] n))) hτ
  change (coordinates R S N).hom
      (edge23 R S N τ (edge12 R S N τ ((1 : triple R S) ⊗ₜ[S, (vertex1 R S).hom] n))) =
    (coordinates R S N).hom
      (edge13 R S N τ ((1 : triple R S) ⊗ₜ[S, (vertex1 R S).hom] n)) at hn
  rw [edge_tmul, coordinates_edge23_lift12, edge_tmul, coordinates_lift13] at hn
  change (comonad R S).toFunctor.map (homEquiv R S N τ) (homEquiv R S N τ n) =
    (comonad R S).δ.app N (homEquiv R S N τ n)
  simpa only [homEquiv_value] using hn

/-- Original overlap data with its actual diagonal and triple equations
produces a genuine coalgebra for the original scalar-extension adjunction.
Neither coalgebra axiom is an input disguised as overlap data. -/
@[expose] def coalgebra (τ : first R S N ⟶ second R S N)
    (hdiag : τ ≫ AffineOverlapDiagonal318.secondEvaluation R S N =
      AffineOverlapDiagonal318.firstEvaluation R S N)
    (hτ : Cocycle R S N τ) : AffineCoalgebraModule318.Data (algebraMap R S) where
  A := N
  a := homEquiv R S N τ
  counit := AffineOverlapDiagonal318.counit_of_diagonal R S N τ hdiag
  coassoc := (coassoc_of_cocycle R S N τ hτ).symm

lemma coalgebra_object (τ : first R S N ⟶ second R S N)
    (hdiag : τ ≫ AffineOverlapDiagonal318.secondEvaluation R S N =
      AffineOverlapDiagonal318.firstEvaluation R S N)
    (hτ : Cocycle R S N τ) : (coalgebra R S N τ hdiag hτ).A = N := rfl

lemma coalgebra_coaction (τ : first R S N ⟶ second R S N)
    (hdiag : τ ≫ AffineOverlapDiagonal318.secondEvaluation R S N =
      AffineOverlapDiagonal318.firstEvaluation R S N)
    (hτ : Cocycle R S N τ) :
    (coalgebra R S N τ hdiag hτ).a = AffineOverlapCoaction318.homEquiv R S N τ := rfl
end AffineOverlapCoassociativity318
