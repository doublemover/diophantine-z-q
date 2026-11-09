module
public import SchemeBoundaryNaturality318

public section
noncomputable section
namespace TwoChartHOneFunctoriality318
open AlgebraicGeometry CategoryTheory
open MayerVietorisSectionKernel318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y Z : Scheme.{0}}

/-- Composition of the original scheme-H1 pullbacks, proved on an exhaustive actual boundary presentation. -/
theorem pullback_comp (g : X ⟶ Y) (f : Y ⟶ Z) (U V : Z.Opens) (h : U ⊔ V = ⊤)
    (hs : Function.Surjective (sectionBoundary (StructureAdditiveSheaf318.sheaf Z) U V h))
    (x : SheafCohomologyRetraction318.structureH Z 1) :
    SchemeSourceCohomology318.pullback g 1 (SchemeSourceCohomology318.pullback f 1 x) =
      SchemeSourceCohomology318.pullback (g ≫ f) 1 x := by
  obtain ⟨a,rfl⟩ := hs x
  rw [SchemeBoundaryNaturality318.scheme_pullback_sectionBoundary,
    SchemeBoundaryNaturality318.scheme_pullback_sectionBoundary,
    SchemeBoundaryNaturality318.scheme_pullback_sectionBoundary]
  have happ := congrArg (fun k => k a) (Scheme.Hom.comp_app g f (U ⊓ V))
  change sectionBoundary (StructureAdditiveSheaf318.sheaf X)
      ((g ≫ f) ⁻¹ᵁ U) ((g ≫ f) ⁻¹ᵁ V) _
      (g.app (f ⁻¹ᵁ (U ⊓ V)) (f.app (U ⊓ V) a)) =
    sectionBoundary (StructureAdditiveSheaf318.sheaf X)
      ((g ≫ f) ⁻¹ᵁ U) ((g ≫ f) ⁻¹ᵁ V) _ ((g ≫ f).app (U ⊓ V) a)
  exact congrArg (sectionBoundary (StructureAdditiveSheaf318.sheaf X)
    ((g ≫ f) ⁻¹ᵁ U) ((g ≫ f) ⁻¹ᵁ V)
    (InverseImageMayerVietoris318.inverseImage_cover (g ≫ f).base U V h)) happ.symm

/-- Original quotient pullbacks are fixed by any original deck morphism. -/
theorem deck_invariant (g : X ⟶ X) (f : X ⟶ Y) (hgf : g ≫ f = f)
    (U V : Y.Opens) (h : U ⊔ V = ⊤)
    (hs : Function.Surjective (sectionBoundary (StructureAdditiveSheaf318.sheaf Y) U V h))
    (x : SheafCohomologyRetraction318.structureH Y 1) :
    SchemeSourceCohomology318.pullback g 1 (SchemeSourceCohomology318.pullback f 1 x) =
      SchemeSourceCohomology318.pullback f 1 x := by
  rw [pullback_comp g f U V h hs,hgf]

end TwoChartHOneFunctoriality318
