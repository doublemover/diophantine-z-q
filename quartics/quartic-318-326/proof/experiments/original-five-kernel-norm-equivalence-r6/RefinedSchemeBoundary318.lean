module
public import MayerVietorisCoverRefinement318
public import AffineChartPullbackScalars318
public import AffineChartRingSections318

public section
noncomputable section
namespace RefinedSchemeBoundary318
open AlgebraicGeometry CategoryTheory
open MayerVietorisSectionKernel318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A source cover only needs to refine the actual inverse-image target cover. -/
theorem pullback_boundary {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U V : Y.Opens) (h : U ⊔ V = ⊤) (U' V' : X.Opens) (h' : U' ⊔ V' = ⊤)
    (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (x : Γ(Y,U ⊓ V)) :
    SchemeSourceCohomology318.pullback f 1
      (sectionBoundary (StructureAdditiveSheaf318.sheaf Y) U V h x) =
    sectionBoundary (StructureAdditiveSheaf318.sheaf X) U' V' h'
      (f.appLE (U ⊓ V) (U' ⊓ V') (inf_le_inf hU hV) x) := by
  rw [SchemeBoundaryNaturality318.scheme_pullback_sectionBoundary]
  exact (MayerVietorisCoverRefinement318.sectionBoundary_refinement
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) U' V'
    (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) h' hU hV
    (StructureAdditiveSheaf318.sheaf X) (f.app (U ⊓ V) x)).symm

/-- General affine chart coordinates commute with appLE on proved-equal original image opens. -/
theorem affine_coordinates {X Y : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (f : X ⟶ Y) (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
    (k : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion k]
    (a : A →+* B) (hsq : j ≫ f = Spec.map (CommRingCat.ofHom a) ≫ k)
    (U : Y.Opens) (V : X.Opens) (hU : k ''ᵁ ⊤ = U) (hV : j ''ᵁ ⊤ = V)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : A) :
    f.appLE U V hVU (AffineChartRingSections318.equivalenceOn k U hU x) =
      AffineChartRingSections318.equivalenceOn j V hV (a x) := by
  subst U
  subst V
  exact AffineChartPullbackScalars318.affine_scalar (CommRingCat.ofHom a) f j k hsq hVU x

end RefinedSchemeBoundary318
