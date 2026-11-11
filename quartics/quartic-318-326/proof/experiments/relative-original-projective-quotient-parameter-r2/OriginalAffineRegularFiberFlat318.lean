module
public import OriginalAffineSectionFlat318
public import RankOneEvaluationFiber318
public import OriginalAffineRankOneCommutation318
public section
noncomputable section
namespace OriginalAffineRegularFiberFlat318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
variable (R B : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ B]
local notation "S" => (R ⊗[ℚ] B)
variable (L : Line (Spec (CommRingCat.of S)))
local notation "P" => OriginalLineAffineModel318.sections (CommRingCat.of S) L
local instance : Module R P := Module.compHom P (algebraMap R S)
local instance : IsScalarTower R S P := IsScalarTower.of_compHom ..
variable (s : P)

/-- The same original section-multiplication map over the coefficient
ring. Its field-fiber injectivity is the intrinsic regular-section test. -/
abbrev section := RankOneEvaluationFiber318.section R S P s

/-- Genuine flatness of the ORIGINAL affine zero projection from the
original section-map's residue regularity. Actual rank-one commutation
is now supplied by original principal frames, and dual-evaluation
injectivity is derived by the same finite dual frame after base change. -/
lemma projection_flat
    (hs : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective ((section R B L s).baseChange (R ⧸ m))) :
    Flat (OriginalAffineSectionFlat318.projection R B L s) := by
  letI := (OriginalLineAffineModel318.properties (CommRingCat.of S) L).1
  let F := FiniteProjectiveEvaluationFrame318.frame S P
  apply OriginalAffineSectionFlat318.projection_flat R B L s
  intro m hm
  exact RankOneEvaluationFiber318.evaluation_injective R S P (R ⧸ m) F s
    (fun φ x => OriginalAffineRankOneCommutation318.commutation (CommRingCat.of S) L φ s x)
    (hs m hm)
end OriginalAffineRegularFiberFlat318
