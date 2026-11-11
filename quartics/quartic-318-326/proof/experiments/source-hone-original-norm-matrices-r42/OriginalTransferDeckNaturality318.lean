module
public import OriginalOpenTraceDeck318
public import AffineHOneComparison318
public import StableCoverBoundary318

public section
noncomputable section
namespace OriginalTransferDeckNaturality318
open AlgebraicGeometry CategoryTheory Opposite
open MayerVietorisSectionKernel318
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) [IsAffineHom f]

/-- The existing source transfer sends the original source boundary to the
original target boundary of the very same coefficient-sheaf map. -/
theorem transfer_boundary
    (r : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y)
    (U V : Y.Opens) (h : U ⊔ V = ⊤) (s : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    AffineHOneComparison318.transfer f r
      (sectionBoundary (StructureAdditiveSheaf318.sheaf X) (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) s) =
    sectionBoundary (StructureAdditiveSheaf318.sheaf Y) U V h (r.hom.app (op (U ⊓ V)) s) := by
  have hc := SchemeBoundaryNaturality318.comparison_sectionBoundary f.base
    (StructureAdditiveSheaf318.sheaf X) U V h s
  change (AffineHOneComparison318.equivalence f)
    (sectionBoundary (StructureAdditiveSheaf318.pushed f) U V h s) = _ at hc
  rw [← hc]
  change Sheaf.H.map r 1 ((AffineHOneComparison318.equivalence f).symm
    ((AffineHOneComparison318.equivalence f)
      (sectionBoundary (StructureAdditiveSheaf318.pushed f) U V h s))) = _
  rw [AddEquiv.symm_apply_apply]
  exact (MayerVietorisCoefficientNaturality318.sectionBoundary_naturality r U V h s).symm

/-- Whole-H1 deck invariance is derived from exact trace invariance on all
original section rings and an affine inverse-image cover. -/
theorem transfer_invariant [IsIntegral Y] [IsDominant f]
    (r : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y)
    (e : X ≅ X) (he : e.hom ≫ f = f)
    (hr : ∀ (W : Y.Opens) (s : Γ(X,f ⁻¹ᵁ W)),
      r.hom.app (op W)
        (e.hom.appLE (f ⁻¹ᵁ W) (f ⁻¹ᵁ W)
          (le_of_eq (OriginalOpenTraceDeck318.preimage f e he W).symm) s) = r.hom.app (op W) s)
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤)
    (y : SheafCohomologyRetraction318.structureH X 1) :
    AffineHOneComparison318.transfer f r (SchemeSourceCohomology318.pullback e.hom 1 y) =
      AffineHOneComparison318.transfer f r y := by
  obtain ⟨s,rfl⟩ := AffineCoverHOnePresentation318.boundary_surjective
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (hU.preimage f) (hV.preimage f)
    (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) y
  change AffineHOneComparison318.transfer f r (SchemeSourceCohomology318.pullback e.hom 1
    (sectionBoundary (StructureAdditiveSheaf318.sheaf X) (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) _ s)) =
    AffineHOneComparison318.transfer f r
      (sectionBoundary (StructureAdditiveSheaf318.sheaf X) (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) _ s)
  rw [StableCoverBoundary318.pullback_stable_boundary e.hom _ _ _
    (OriginalOpenTraceDeck318.preimage f e he U) (OriginalOpenTraceDeck318.preimage f e he V)]
  rw [transfer_boundary,transfer_boundary]
  congr 1
  exact hr (U ⊓ V) s

end OriginalTransferDeckNaturality318
