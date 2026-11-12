module
public import OriginalFppfUnitLocalSurjective318
public section
noncomputable section
namespace ContactDifferenceLocalSurjective318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The genuine all-bound Cartier difference Abel transformation is
locally surjective on the ACTUAL original fppf line-class sheaf, on ALL
scheme tests and for arbitrary sheaf elements, including elements not
given by a global line representative. -/
instance locallySurjective : Presheaf.IsLocallySurjective
    (RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)))
    (ContactCartierDifferenceAbel318.transformation c) :=
  LocalImageCoverDescent318.from_local_source _ (ContactCartierDifferenceAbel318.transformation c)
    (Functor.whiskerRight (RelativeFppfLineSheaf318.unit p) (forget CommGrpCat.{1}))
    (ContactDifferenceNaiveImage318.covering c)
end ContactDifferenceLocalSurjective318
