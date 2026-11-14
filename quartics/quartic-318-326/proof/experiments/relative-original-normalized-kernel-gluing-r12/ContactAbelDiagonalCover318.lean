module
public import WholeGeometricDiagonalImage318
public section
noncomputable section
namespace ContactAbelDiagonalCover318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "v" => ContactCartierDifferenceAbel318.transformation c
variable (D E : A.obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "π" => ContactRelationProjectionImage318.projection R c L K
/-- Every WHOLE point of the actual original Abel diagonal fiber is
locally in the image of the SAME universal original Isom projection.
Covering of this sieve does not assert that π itself is flat. -/
lemma covering (T : Over Q) (f : T ⟶ B)
    (he : (ContactDifferenceSheafEpimorphism318.target c).obj.map f.op (v.app (op B) D)=
      (ContactDifferenceSheafEpimorphism318.target c).obj.map f.op (v.app (op B) E)) :
    (MorphismImageSieve318.image π).pullback f ∈ RelativeFppfLineSheaf318.topology Q T := by
  rw [MorphismImageSieve318.pullback_image]
  apply (ContactPicardGeometricCoverCriterion318.pullback_iff_covering R c L K T f).mp
  let V := OriginalAbsoluteLinePresheaf318.value (ContactIntrinsicDifferentials318.structureMap c)
  have hd : V.app (op B) (classOf L)=v.app (op B) D :=
    ContactDifferenceNaiveClass318.sheaf_value c B D
  have hk : V.app (op B) (classOf K)=v.app (op B) E :=
    ContactDifferenceNaiveClass318.sheaf_value c B E
  have hx := ConcreteCategory.congr_hom (V.naturality f.op) (classOf L)
  have hy := ConcreteCategory.congr_hom (V.naturality f.op) (classOf K)
  rw [hd] at hx
  rw [hk] at hy
  exact hx.trans (he.trans hy.symm)
end ContactAbelDiagonalCover318
