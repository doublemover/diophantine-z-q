module
public import OriginalAffineSheafElementExt318
public section
noncomputable section
namespace ContactGeometricIsomInvariant318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
variable (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
/-- Concrete invariance on the SAME actual universal Isom scheme for
every affine original pair of full Cartier-difference line families.
The source relation scheme is produced, not a representation premise. -/
@[expose] def Invariant : Prop := ∀ (R : CommRingCat.{0}) (hR : Algebra ℚ R),
  letI := hR
  ∀ D E : A.obj (op (Over.mk (baseMap R))),
  F.obj.map (ContactRelationProjectionImage318.projection R c
    (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) D)
    (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) E)).op
      (a.app (op (Over.mk (baseMap R))) D)=
  F.obj.map (ContactRelationProjectionImage318.projection R c
    (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) D)
    (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) E)).op
      (a.app (op (Over.mk (baseMap R))) E)
/-- Actual universal-relation invariance suffices on every affine base:
the original Abel fiber is covered by the SAME geometric image sieve. -/
lemma affine_kernel (ha : Invariant c F a) (R : CommRingCat.{0}) [Algebra ℚ R]
    (D E : A.obj (op (Over.mk (baseMap R))))
    (he : (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk (baseMap R))) D=
      (ContactCartierDifferenceAbel318.transformation c).app (op (Over.mk (baseMap R))) E) :
    a.app (op (Over.mk (baseMap R))) D=a.app (op (Over.mk (baseMap R))) E := by
  apply WholeSheafGeometricImageExt318.image_ext J F
    (ContactRelationProjectionImage318.projection R c
      (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) D)
      (ContactDifferenceNaiveClass318.line c (Over.mk (baseMap R)) E))
  · rw [MorphismImageSieve318.generated]
    exact (ContactBoundedAbelGeometricRelation318.abel_iff_generated_covering R c D E).mp he
  · exact ha R inferInstance D E
end ContactGeometricIsomInvariant318
