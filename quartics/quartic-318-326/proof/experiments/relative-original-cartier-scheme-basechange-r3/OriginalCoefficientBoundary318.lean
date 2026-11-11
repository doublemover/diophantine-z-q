module
public import OriginalCoefficientCohomology318
public import MayerVietorisCoefficientNaturality318
public section
noncomputable section
namespace OriginalCoefficientBoundary318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalCoefficientCohomology318
variable (R : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R) (L : Line X)
local instance (U : X.Opens) : Module R Γ(L.object,U) := sectionModule R p L U
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) := cohomologyModule R p L 1

/-- The ACTUAL derived boundary is linear for the original structural
coefficient actions, by actual Mayer-Vietoris coefficient naturality.
Unlike the rational case, no uniqueness of a rational action is used. -/
@[expose] def linear (U V : X.Opens) (h : U ⊔ V = ⊤) :
    Γ(L.object,U ⊓ V) →ₗ[R] NonreducedLineMayerVietoris318.H1 L where
  __ := NonreducedLineMayerVietoris318.boundary L U V h
  map_smul' r s := by
    change NonreducedLineMayerVietoris318.boundary L U V h (scalar R p (U ⊓ V) r • s) =
      Sheaf.H.map (multiply R p L r) 1 (NonreducedLineMayerVietoris318.boundary L U V h s)
    rw [← multiply_apply]
    simpa only [NonreducedLineMayerVietoris318.boundary] using
      MayerVietorisCoefficientNaturality318.sectionBoundary_naturality (multiply R p L r) U V h s
end OriginalCoefficientBoundary318
