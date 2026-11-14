module
public import WholeSheafGeometricImageExt318
public import OriginalAffineCoefficientCover318
public section
noncomputable section
namespace OriginalAffineSheafElementExt318
open AlgebraicGeometry CategoryTheory Opposite
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
/-- Arbitrary Type-valued fppf sheaf elements are detected on the actual
original affine coefficient cover, not only on fields or reduced tests. -/
lemma ext (F : Sheaf J (Type 1)) (B : Over Q) (x y : F.obj.obj (op B))
    (h : ∀ i,F.obj.map (OriginalAffineCoefficientCover318.arrow B.hom i).op x=
      F.obj.map (OriginalAffineCoefficientCover318.arrow B.hom i).op y) : x=y := by
  have ht := (isSheaf_iff_isSheaf_of_type F.obj).mp F.property
  apply (ht.isSheafFor (Presieve.ofArrows (OriginalAffineCoefficientCover318.object B.hom)
    (OriginalAffineCoefficientCover318.arrow B.hom))
    (OriginalAffineCoefficientCover318.covering B.hom)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact h i
end OriginalAffineSheafElementExt318
