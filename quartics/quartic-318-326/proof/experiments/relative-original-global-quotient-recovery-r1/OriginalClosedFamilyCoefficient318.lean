module
public import RelativeCoefficientCartesian318
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public section
noncomputable section
namespace OriginalClosedFamilyCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (k R S : CommRingCat.{u}) [Algebra k R] [Algebra k S]
  (f : R →ₐ[k] S) {X Z : Scheme.{u}} (p : X ⟶ Spec k)
  (i : Z ⟶ RelativeOriginalAffineChart318.family k R p) [IsClosedImmersion i]
local notation "qR" => pullback.snd p (RelativeOriginalAffineChart318.baseMap k R)
local notation "qS" => pullback.snd p (RelativeOriginalAffineChart318.baseMap k S)
local notation "b" => RelativeCoefficientChange318.familyMap k R S f p
abbrev family := pullback i b
abbrev into : family k R S f p i ⟶ RelativeOriginalAffineChart318.family k S p := pullback.snd i b
abbrev toFamily : family k R S f p i ⟶ Z := pullback.fst i b
abbrev projection : family k R S f p i ⟶ Spec S := into k R S f p i ≫ qS
instance closed : IsClosedImmersion (into k R S f p i) := inferInstance
@[reassoc] lemma into_square : into k R S f p i ≫ b=toFamily k R S f p i ≫ i :=
  pullback.condition.symm
lemma cartesian : IsPullback (toFamily k R S f p i) (projection k R S f p i)
    (i ≫ qR) (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
  (IsPullback.of_hasPullback i b).paste_vert (RelativeCoefficientCartesian318.cartesian k R S f p)
instance finite [IsFinite (i ≫ qR)] : IsFinite (projection k R S f p i) :=
  MorphismProperty.of_isPullback (cartesian k R S f p i) inferInstance
instance flat [Flat (i ≫ qR)] : Flat (projection k R S f p i) :=
  MorphismProperty.of_isPullback (cartesian k R S f p i) inferInstance
instance presentation [LocallyOfFinitePresentation (i ≫ qR)] :
    LocallyOfFinitePresentation (projection k R S f p i) :=
  MorphismProperty.of_isPullback (cartesian k R S f p i) inferInstance
lemma rank [IsFinite (i ≫ qR)] [Flat (i ≫ qR)] (s : Spec S) :
    (projection k R S f p i).finrank s=(i ≫ qR).finrank (Spec.map (CommRingCat.ofHom f.toRingHom) s) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian k R S f p i) s
end OriginalClosedFamilyCoefficient318
