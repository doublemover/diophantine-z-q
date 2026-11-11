module
public import SourceCohomologyComparison318
public import SheafCohomologyRetraction318

public section
noncomputable section
namespace SchemeSourceCohomology318
open AlgebraicGeometry CategoryTheory
open SheafCohomologyRetraction318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme} (f : X ⟶ Y)

/-- Canonical comparison from actual direct-image cohomology to actual source cohomology. -/
@[expose] def comparison (n : ℕ) : pushedH f n →+ structureH X n :=
  SourceCohomologyComparison318.comparison f.base (StructureAdditiveSheaf318.sheaf X) n

/-- The full scheme-cohomology pullback with its original structure-sheaf map. -/
@[expose] def pullback (n : ℕ) : structureH Y n →+ structureH X n :=
  (comparison f n).comp (SheafCohomologyRetraction318.pullback f n)

theorem pullback_factorization (n : ℕ) (x : structureH Y n) :
    pullback f n x = comparison f n (SheafCohomologyRetraction318.pullback f n x) := rfl

theorem comparison_zero_bijective : Function.Bijective (comparison f 0) :=
  SourceCohomologyComparison318.comparison_zero_bijective _ _

theorem comparison_one_injective : Function.Injective (comparison f 1) :=
  SourceCohomologyComparison318.comparison_one_injective _ _

/-- An actual sheaf retraction now gives injectivity into source H¹ itself. -/
theorem pullback_one_injective_of_retraction
    (r : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 _) :
    Function.Injective (pullback f 1) :=
  (comparison_one_injective f).comp
    (SheafCohomologyRetraction318.pullback_injective f r h 1)

end SchemeSourceCohomology318
