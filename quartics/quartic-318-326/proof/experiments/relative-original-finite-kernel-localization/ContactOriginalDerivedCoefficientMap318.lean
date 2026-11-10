module
public import ContactCoefficientWholeOpens318
public import OriginalLineDerivedFunctoriality318
public import OriginalLineDerivedNaturality318
public import OriginalBoundaryOpenTransport318
public import ContactOriginalHOneBaseChange318
public section
noncomputable section
namespace ContactOriginalDerivedCoefficientMap318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open NonreducedLineRestriction318 ContactRelativeCoefficientChange318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactCoefficientWholeOpens318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
abbrev pulled := LineSheafPullback318.line (curveMap R S f c) L

/-- Independent original derived coefficient pullback. No Cech cover,
frame, or tensor comparison is used to define it. -/
@[expose] def map (n : ℕ) : Sheaf.H (additive L) n →+
    Sheaf.H (additive (pulled R S f c L)) n :=
  OriginalLineDerivedPullback318.map (curveMap R S f c) L n

/-- The actual module unit on the FULL ambient overlap, with only the
proved inverse-image equality transporting its target open. -/
@[expose] def overlapPull : Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) →+
    Γ((pulled R S f c L).object,finiteOpen S c ⊓ infinityOpen S c) :=
  (((pulled R S f c L).object.presheaf.map
    (eqToHom (overlap_preimage R S f c).symm).op).hom).comp
      (((Scheme.Modules.pullbackPushforwardAdjunction (curveMap R S f c)).unit.app
        L.object).app (finiteOpen R c ⊓ infinityOpen R c)).hom

/-- Actual original derived boundary compatibility on the exact contact
finite/infinity cover. This does NOT assume a coefficient section square. -/
lemma boundary (s : Γ(L.object,finiteOpen R c ⊓ infinityOpen R c)) :
    map R S f c L 1
      (NonreducedLineMayerVietoris318.boundary L (finiteOpen R c) (infinityOpen R c) (cover R c) s) =
    NonreducedLineMayerVietoris318.boundary (pulled R S f c L)
      (finiteOpen S c) (infinityOpen S c) (cover S c) (overlapPull R S f c L s) := by
  rw [map,OriginalLineDerivedPullback318.boundary]
  exact (OriginalBoundaryOpenTransport318.transport (pulled R S f c L)
    ((curveMap R S f c) ⁻¹ᵁ finiteOpen R c) ((curveMap R S f c) ⁻¹ᵁ infinityOpen R c)
    (finiteOpen S c) (infinityOpen S c) _ (cover S c)
    (finite_preimage R S f c) (infinity_preimage R S f c) _).symm

/-- The independent derived map is already normalized on EVERY old
Laurent representative, expressed in original ambient overlap sections. -/
lemma representative (s : ContactOriginalRelativeLineOverlap318.originalSections R c L) :
    map R S f c L 1 (ContactRelativeOriginalDerivedQuotient318.boundary R c L s) =
    NonreducedLineMayerVietoris318.boundary (pulled R S f c L)
      (finiteOpen S c) (infinityOpen S c) (cover S c)
      (overlapPull R S f c L (overlapEquiv R c L s)) :=
  boundary R S f c L (overlapEquiv R c L s)

/-- Since this independent map was defined without a cover, ANY full
cover has its genuine boundary formula, including a different affine
cover or a common refinement. No original chart is privileged. -/
lemma any_cover (U V : (curve R c).Opens) (h : U ⊔ V = ⊤) (s : Γ(L.object,U ⊓ V)) :
    map R S f c L 1 (NonreducedLineMayerVietoris318.boundary L U V h s) =
      NonreducedLineMayerVietoris318.boundary (pulled R S f c L)
        ((curveMap R S f c) ⁻¹ᵁ U) ((curveMap R S f c) ⁻¹ᵁ V)
        (InverseImageMayerVietoris318.inverseImage_cover (curveMap R S f c).base U V h)
        ((OriginalLineDerivedPullback318.unit (curveMap R S f c) L).hom.app (op (U ⊓ V)) s) :=
  OriginalLineDerivedPullback318.boundary _ _ _ _ _ _
end ContactOriginalDerivedCoefficientMap318
