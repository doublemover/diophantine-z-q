module
public import OriginalAffineRegularFiberFlat318
public import ProjectiveFiberwiseInjection318
public import ProjectiveCoefficientRestriction318
public section
noncomputable section
namespace OriginalAffineFiberwiseRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
variable (R B : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ B]
local notation "S" => (R ⊗[ℚ] B)
variable (L : Line (Spec (CommRingCat.of S)))
local notation "P" => OriginalLineAffineModel318.sections (CommRingCat.of S) L
local instance : Module R P := Module.compHom P (algebraMap R S)
local instance : IsScalarTower R S P := IsScalarTower.of_compHom ..
variable (s : P)

/-- Actual regularity of the ORIGINAL line section over the entire
coefficient ring from its genuine residue maps. Original affine line
projectivity and coefficient freeness are constructed, not assumed. -/
lemma regular
    (hs : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective ((OriginalAffineRegularFiberFlat318.section R B L s).baseChange (R ⧸ m))) :
    SectionZeroRegularCoordinate318.Regular S P s := by
  letI : Module.Free R S :=
    Module.Free.of_basis ((Module.Free.chooseBasis ℚ B).baseChange R)
  letI := (OriginalLineAffineModel318.properties (CommRingCat.of S) L).1
  letI : Module.Projective R P := ProjectiveCoefficientRestriction318.projective R S P
  exact ProjectiveFiberwiseInjection318.injective
    (OriginalAffineRegularFiberFlat318.section R B L s) hs
end OriginalAffineFiberwiseRegular318
