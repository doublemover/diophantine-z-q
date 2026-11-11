module
public import ContactNormalizedBoundedRecovery318
public section
noncomputable section
namespace CartierAmbientIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z X Y : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (e : X ≅ Y) (hp : OriginalRegularClosedCharts318.Property p)
abbrev into := p ≫ e.hom
include hp in
lemma regular : OriginalRegularClosedCharts318.Property (into p e) :=
  RegularClosedSquareIso318.transport p (into p e) (Iso.refl _) e
    (by simp only [Iso.refl_hom,Category.id_comp]; rfl) hp
lemma cartesian : IsPullback (𝟙 Z) (into p e) p e.inv :=
  IsPullback.of_horiz_isIso ⟨by simp only [into,Category.id_comp,Category.assoc,Iso.hom_inv_id,Category.comp_id]⟩
local notation "D" => CartierCanonicalSection318.divisorLine p hp
local notation "s" => CartierCanonicalSection318.section p hp
@[expose] def zeroCharts : SectionZeroChartData318.Data (into p e)
    (LineSheafPullback318.line e.inv D) (OriginalSectionPullbackComposition318.pull e.inv D.object s) :=
  SectionZeroPullbackData318.data p (into p e) (𝟙 Z) e.inv (cartesian p e) D s
    (CartierCanonicalZeroCharts318.data p hp)
lemma divisor_class : classOf (CartierCanonicalSection318.divisorLine (into p e) (regular p e hp))=
    classOf (LineSheafPullback318.line e.inv D) :=
  SectionZeroCartierKernel318.divisor_class (into p e) _ _ (zeroCharts p e hp) (regular p e hp)
/-- The actual Cartier divisor line is unchanged by an exact ambient
isomorphism, with its literal forward and inverse maps retained. -/
lemma pulled_class : classOf (LineSheafPullback318.line e.hom
    (CartierCanonicalSection318.divisorLine (into p e) (regular p e hp)))=classOf D := by
  change LineSheafPullback318.pullback e.hom
    (classOf (CartierCanonicalSection318.divisorLine (into p e) (regular p e hp)))=_
  rw [divisor_class]
  change LineSheafPullback318.pullback e.hom (LineSheafPullback318.pullback e.inv (classOf D))=_
  rw [← LineClassPullbackLaws318.pullback_composition,Iso.hom_inv_id,LineClassPullbackLaws318.pullback_identity]
end CartierAmbientIso318
