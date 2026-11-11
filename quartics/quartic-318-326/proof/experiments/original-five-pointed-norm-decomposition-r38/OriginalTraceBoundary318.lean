module
public import OriginalThickenedNormTraceSquare318
public section
noncomputable section
namespace OriginalTraceBoundary318
open AlgebraicGeometry CategoryTheory Opposite
open SheafCohomologyRetraction318 MayerVietorisSectionKernel318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsAffineHom f]
    (t : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y)
    (U V : Y.Opens) (hc : U ⊔ V = ⊤)
/-- The OLD comparison inverse sends the original source boundary to the
original direct-image boundary. No new identification of H1 is selected. -/
lemma inverse_comparison (a : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    (AffineHOneComparison318.equivalence f).symm
      (AffineCoverHOnePresentation318.boundary (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V hc) a) =
    sectionBoundary (StructureAdditiveSheaf318.pushed f) U V hc a := by
  apply (AffineHOneComparison318.equivalence f).injective
  rw [AddEquiv.apply_symm_apply]
  exact (SchemeBoundaryNaturality318.comparison_sectionBoundary f.base
    (StructureAdditiveSheaf318.sheaf X) U V hc a).symm
/-- The SAME original source transfer, with its actual comparison inverse,
acts on every old representative by the SAME original coefficient trace.
The finite-minus-infinity convention is unchanged. -/
lemma transfer_boundary (a : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    AffineHOneComparison318.transfer f t
      (AffineCoverHOnePresentation318.boundary (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V hc) a) =
    AffineCoverHOnePresentation318.boundary U V hc (t.hom.app (op (U ⊓ V)) a) := by
  change Sheaf.H.map t 1 ((AffineHOneComparison318.equivalence f).symm _) = _
  rw [inverse_comparison]
  exact (MayerVietorisCoefficientNaturality318.sectionBoundary_naturality t U V hc a).symm
end OriginalTraceBoundary318
