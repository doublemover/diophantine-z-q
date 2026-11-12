module
public import SectionZeroChartData318
public section
noncomputable section
namespace CartierCanonicalZeroCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartierCanonicalSection318 CartierFramedAffineCover318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (hp : OriginalRegularClosedCharts318.Property p)
local notation "D" => divisorLine p hp
local notation "s" => section p hp
@[expose] def zero (i : Index p hp) :
    Spec (CommRingCat.of (ring p hp i ⧸ SectionZeroAffineRefinement318.sectionIdeal
      (ring p hp i) (into p hp i) D s)) ⟶ Z :=
  SectionZeroAffineRefinement318.transportInto (ring p hp i)
    (CartierCanonicalSectionIdeal318.ideal p hp (ring p hp i) (into p hp i) i.frame (frame_le p hp i)).symm
    (AffineClosedRestrictionChart318.into p (ring p hp i) (into p hp i))
lemma cartesian (i : Index p hp) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (SectionZeroAffineRefinement318.sectionIdeal
      (ring p hp i) (into p hp i) D s)))) (zero p hp i) (into p hp i) p :=
  SectionZeroAffineRefinement318.transport_square (ring p hp i) (into p hp i) p
    (CartierCanonicalSectionIdeal318.ideal p hp (ring p hp i) (into p hp i) i.frame (frame_le p hp i)).symm
    (AffineClosedRestrictionChart318.into p (ring p hp i) (into p hp i))
    (AffineClosedRestrictionChart318.cartesian p (ring p hp i) (into p hp i))
/-- The canonical O(D) section realizes the WHOLE original Cartier
closed subscheme, on a produced complete affine cover. -/
@[expose] def data : SectionZeroChartData318.Data p D s where
  Index := Index p hp
  ring := ring p hp
  into := into p hp
  open_into _ := inferInstance
  cover := cover p hp
  zero := zero p hp
  cartesian := cartesian p hp
end CartierCanonicalZeroCharts318
