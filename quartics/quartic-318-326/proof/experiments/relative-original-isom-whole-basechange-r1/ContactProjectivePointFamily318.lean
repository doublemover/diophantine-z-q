module
public import OriginalAffineCoefficientIdentity318
public section
noncomputable section
namespace ContactProjectivePointFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (x : ContactProjectiveParameterPoint318.Point c n S)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactProjectiveParameterStructure318.structureMap c n
local notation "q" => ContactProjectiveUniversalGluing318.original c n
abbrev family := OriginalClosedFamilyRestriction318.family p b x.val q
abbrev toFamily := OriginalClosedFamilyRestriction318.toFamily p b x.val q
abbrev projection := OriginalClosedFamilyRestriction318.projection p b x.val q
abbrev into : family c n S x ⟶ ContactRelativeLinearOpenChart318.curve S c :=
  OriginalClosedFamilyRestriction318.into p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property q
abbrev sourceMap : ContactRelativeLinearOpenChart318.curve S c ⟶ ContactProjectiveUniversalAmbient318.scheme c n :=
  RelativeSchemeCoefficient318.map p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property
lemma cartesian : IsPullback (toFamily c n S x) (into c n S x) q (sourceMap c n S x) :=
  OriginalClosedFamilyRestriction318.cartesian _ _ _ _ _ _
@[reassoc] lemma into_base : into c n S x ≫ ContactRelativeLinearOpenChart318.projection S c=projection c n S x :=
  OriginalClosedFamilyRestriction318.into_base _ _ _ _ _ _
instance closed : IsClosedImmersion (into c n S x) := inferInstance
instance finite : IsFinite (projection c n S x) := inferInstance
instance flat : Flat (projection c n S x) := inferInstance
instance presentation : LocallyOfFinitePresentation (projection c n S x) := inferInstance
abbrev idealSheaf : (ContactRelativeLinearOpenChart318.curve S c).IdealSheafData := (into c n S x).ker
end ContactProjectivePointFamily318
