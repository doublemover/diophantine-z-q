module
public import SchemeBoundaryNaturality318
public import NonreducedLineMayerVietoris318
public section
noncomputable section
namespace OriginalLineDerivedPullback318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open NonreducedLineRestriction318 SheafInverseImageConstants318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : Line Y)

/-- Forget only scalars from the genuine module-pullback unit. Its target
is the actual topological direct image of the original pulled-back line. -/
@[expose] def unit : additive L ⟶
    (directImage f.base).obj (additive (LineSheafPullback318.line f L)) :=
  (SheafOfModules.toSheaf Y.ringCatSheaf).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.object)

lemma unit_apply (U : Y.Opens) (s : Γ(L.object,U)) :
    (unit f L).hom.app (op U) s =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.object).app U) s := rfl

/-- Actual derived pullback, constructed before choosing any cover or
Cech quotient: Ext inverse image, integer-sheaf comparison, original
counit, and the original module-pullback unit. -/
@[expose] def map (n : ℕ) : Sheaf.H (additive L) n →+
    Sheaf.H (additive (LineSheafPullback318.line f L)) n :=
  (SourceCohomologyComparison318.comparison f.base
    (additive (LineSheafPullback318.line f L)) n).comp (Sheaf.H.map (unit f L) n)

/-- The same cover-free derived map commutes with the genuine boundary
for EVERY full two-open cover, with the literal inverse-image opens. -/
lemma boundary (U V : Y.Opens) (h : U ⊔ V = ⊤) (s : Γ(L.object,U ⊓ V)) :
    map f L 1 (NonreducedLineMayerVietoris318.boundary L U V h s) =
      NonreducedLineMayerVietoris318.boundary (LineSheafPullback318.line f L)
        (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V h)
        ((unit f L).hom.app (op (U ⊓ V)) s) := by
  change SourceCohomologyComparison318.comparison f.base _ 1
    (Sheaf.H.map (unit f L) 1
      (MayerVietorisSectionKernel318.sectionBoundary (additive L) U V h s)) = _
  rw [← MayerVietorisCoefficientNaturality318.sectionBoundary_naturality]
  exact SchemeBoundaryNaturality318.comparison_sectionBoundary f.base _ U V h _

/-- On a full two-affine cover, the original boundary determines the
actual derived map uniquely. This is a theorem about arbitrary original
lines, not a chosen scalar basis or a quotient-defined substitute. -/
lemma unique (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤)
    (a : NonreducedLineMayerVietoris318.H1 L →+
      NonreducedLineMayerVietoris318.H1 (LineSheafPullback318.line f L))
    (ha : ∀ s, a (NonreducedLineMayerVietoris318.boundary L U V h s) =
      NonreducedLineMayerVietoris318.boundary (LineSheafPullback318.line f L)
        (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover f.base U V h)
        ((unit f L).hom.app (op (U ⊓ V)) s)) : a = map f L 1 := by
  ext x
  obtain ⟨s,rfl⟩ := NonreducedLineMayerVietoris318.boundary_surjective L U V hU hV h x
  exact (ha s).trans (boundary f L U V h s).symm
end OriginalLineDerivedPullback318
