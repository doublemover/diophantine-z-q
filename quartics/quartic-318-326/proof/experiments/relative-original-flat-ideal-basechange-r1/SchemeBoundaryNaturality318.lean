module
public import InverseImageTerminalCoherence318
public import InverseImageMayerVietoris318
public import MayerVietorisCoefficientNaturality318
public import AffineCoverHOnePresentation318
public import SchemeSourceCohomology318

public section
noncomputable section
namespace SchemeBoundaryNaturality318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
open SheafInverseImageConstants318 MayerVietorisSectionKernel318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original global direct-image comparison commutes with the original full-cover boundary. -/
theorem comparison_boundary {X Y : TopCat.{0}} (f : X ⟶ Y) (F : ASheaf (X:=X))
    (U V : Opens Y) (h : U ⊔ V = ⊤) (x : ((directImage f).obj F).H' 0 (U ⊓ V)) :
    SourceCohomologyComparison318.comparison f F 1
      (OpenMayerVietoris318.boundary ((directImage f).obj F) U V h x) =
    OpenMayerVietoris318.boundary F ((Opens.map f).obj U) ((Opens.map f).obj V)
      (InverseImageMayerVietoris318.inverseImage_cover f U V h)
      (InverseImageLocalCohomology318.comparison f F (U ⊓ V) 0 x) := by
  change SourceCohomologyComparison318.comparison f F 1
      (TerminalLocalCohomology318.equivalence Y ((directImage f).obj F) 1
        ((InverseImageMayerVietoris318.targetSquare U V h).δ ((directImage f).obj F) 0 1 rfl x)) = _
  rw [InverseImageTerminalCoherence318.comparison_terminal,
    InverseImageMayerVietoris318.delta_comparison]
  rfl

/-- On literal sections, no change of representative or scalar is present. -/
theorem comparison_sectionBoundary {X Y : TopCat.{0}} (f : X ⟶ Y) (F : ASheaf (X:=X))
    (U V : Opens Y) (h : U ⊔ V = ⊤)
    (x : ((directImage f).obj F).obj.obj (op (U ⊓ V))) :
    SourceCohomologyComparison318.comparison f F 1
      (sectionBoundary ((directImage f).obj F) U V h x) =
    sectionBoundary F ((Opens.map f).obj U) ((Opens.map f).obj V)
      (InverseImageMayerVietoris318.inverseImage_cover f U V h) x := by
  change SourceCohomologyComparison318.comparison f F 1
    (OpenMayerVietoris318.boundary ((directImage f).obj F) U V h
      ((zeroAddEquiv ((directImage f).obj F) (U ⊓ V)).symm x)) = _
  rw [comparison_boundary]
  have hz : InverseImageLocalCohomology318.comparison f F (U ⊓ V) 0
      ((zeroAddEquiv ((directImage f).obj F) (U ⊓ V)).symm x) =
    (zeroAddEquiv F (((Opens.map f).obj U) ⊓ ((Opens.map f).obj V))).symm x := by
    change InverseImageLocalCohomology318.comparison f F (U ⊓ V) 0
      ((zeroAddEquiv ((directImage f).obj F) (U ⊓ V)).symm x) =
        (zeroAddEquiv F ((Opens.map f).obj (U ⊓ V))).symm x
    apply (zeroAddEquiv F ((Opens.map f).obj (U ⊓ V))).injective
    rw [InverseImageLocalCohomology318.comparison_zero_sections,
      AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  rw [hz]
  rfl

/-- The genuine scheme-cohomology pullback takes a boundary to the boundary of its actual section pullback. -/
theorem scheme_pullback_sectionBoundary {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U V : Y.Opens) (h : U ⊔ V = ⊤) (x : Γ(Y,U ⊓ V)) :
    SchemeSourceCohomology318.pullback f 1
      (sectionBoundary (StructureAdditiveSheaf318.sheaf Y) U V h x) =
    sectionBoundary (StructureAdditiveSheaf318.sheaf X) (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
      (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) (f.app (U ⊓ V) x) := by
  change SourceCohomologyComparison318.comparison f.base (StructureAdditiveSheaf318.sheaf X) 1
    (Sheaf.H.map (StructureAdditiveSheaf318.pullback f) 1
      (sectionBoundary (StructureAdditiveSheaf318.sheaf Y) U V h x)) = _
  rw [← MayerVietorisCoefficientNaturality318.sectionBoundary_naturality]
  exact comparison_sectionBoundary f.base (StructureAdditiveSheaf318.sheaf X) U V h _

/-- When the two charts are affine this is the same boundary used by the concrete source presentation. -/
theorem scheme_pullback_boundary {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (U V : Y.Opens) (h : U ⊔ V = ⊤) (x : Γ(Y,U ⊓ V)) :
    SchemeSourceCohomology318.pullback f 1 (AffineCoverHOnePresentation318.boundary U V h x) =
      AffineCoverHOnePresentation318.boundary (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) (f.app (U ⊓ V) x) :=
  scheme_pullback_sectionBoundary f U V h x

end SchemeBoundaryNaturality318
