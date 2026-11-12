module
public import ContactRelativeBoundedLine318
public section
noncomputable section
namespace ContactNormalizedRelativeBounded318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "N" => ContactNormalizedParameterCompact318.bound R c L hz
local notation "D" => ContactNormalizedBoundedCartier318.data R c L hz
lemma comparison : (RelativeAmbientReassociation318.comparison p (baseMap R) b).hom=
    (ContactNormalizedAbsoluteAmbient318.comparison R c L hz).hom := by
  apply pullback.hom_ext
  · rw [RelativeAmbientReassociation318.first,ContactNormalizedAbsoluteAmbient318.original_projection]
    rfl
  · rw [RelativeAmbientReassociation318.second,ContactNormalizedAbsoluteAmbient318.base_projection]
lemma original_class : classOf (ContactRelativeBoundedLine318.line R c N b D)=
    classOf (ContactNormalizedGlobalIdealLine318.divisorLine R c L hz) := by
  change classOf (LineSheafPullback318.line
    (RelativeAmbientReassociation318.comparison p (baseMap R) b).hom _)=_
  rw [comparison]
  exact ContactNormalizedBoundedDivisor318.original_class R c L hz
lemma original_value : RelativeClassSheafPoint318.value q b
    (OriginalLineAbelTransformation318.point q b (ContactRelativeBoundedLine318.line R c N b D))=
      RelativeClassSheafPoint318.value q b (RelativeClassSheafPoint318.original q b (classOf L)) := by
  have h := congrArg (RelativeLineClassQuotient318.classMap (pullback.snd q b)) (original_class R c L hz)
  change OriginalLineAbelTransformation318.point q b (ContactRelativeBoundedLine318.line R c N b D)=
    OriginalLineAbelTransformation318.point q b (ContactNormalizedGlobalIdealLine318.divisorLine R c L hz) at h
  rw [h]
  exact ContactNormalizedAbelFiber318.original_sheaf_class R c L hz
end ContactNormalizedRelativeBounded318
