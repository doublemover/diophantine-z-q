module
public import CharacterFifthCommonMultiple318
public import FifthBranchDifferential318
public section
noncomputable section
namespace CharacterBranchLocalForm318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CharacterFifthCommonMultiple318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev B (j:Fin 4):=ContactIntrinsicFrames318.BranchRing units j
@[expose] def root (i j:Fin 4):B j:=algebraMap (ContactKummerOrder318.SourceOrder units) (B j)
  (ContactRootReciprocals318.root units i)
@[expose] def unitCoefficient (i j:Fin 4):B j:=
  algebraMap ℚ (B j) (factor i)*FifthBranchUnitCoefficient318.coefficient j
lemma unitCoefficient_unit (i j:Fin 4):IsUnit (unitCoefficient i j):=
  ((factor_unit i).map (algebraMap ℚ (B j))).mul (FifthBranchUnitCoefficient318.coefficient_unit j)
@[expose] def form (i j:Fin 4):KaehlerDifferential ℚ (B j):=
  (algebraMap ℚ (B j) (factor i)*root i j) • FifthBranchDifferential318.form j
lemma frame_value (i j:Fin 4):
    ContactDifferentialFrames318.sourceLocalizationFrame units j (form i j)=unitCoefficient i j*root i j:=by
  rw [form,map_smul,smul_eq_mul,FifthBranchDifferential318.frame_value]
  unfold unitCoefficient
  ring
/-- On every branch other than the omitted character index the actual
local coefficient is a unit on the entire chart. -/
lemma frame_unit (i j:Fin 4) (h:i≠j):IsUnit
    (ContactDifferentialFrames318.sourceLocalizationFrame units j (form i j)):=by
  rw [frame_value]
  exact (unitCoefficient_unit i j).mul (ContactRootReciprocals318.branch_root_unit units i j h)
/-- At the omitted branch the coefficient is exactly unit times its literal
original-root coordinate, not a chosen square root or a punctured-chart unit. -/
lemma omitted_frame_value (i:Fin 4):
    ContactDifferentialFrames318.sourceLocalizationFrame units i (form i i)=
      unitCoefficient i i*ContactFrameNormalization318.sourceCoordinate units i:=by
  rw [frame_value,BranchOriginalCoordinate318.coordinate_eq_root]
  rfl
lemma common_root (i j:Fin 4):ContactOverlapAlgebraMaps318.branchMap units j (root i j)=
    ContactRootReciprocals318.openRoot units i:=
  BranchOverlapLocalization318.toOpen_on_source units j _
/-- Exact actual algebraic differential comparison on the full common open. -/
theorem common_eq (i j:Fin 4):
    AlgHomDifferential318.map (R:=ℚ) (S:=B j) (T:=O)
      (ContactOverlapAlgebraMaps318.branchMap units j) (form i j)=
        FifthFormCommonOpen318.form i:=by
  rw [form,AlgHomDifferential318.map_smul,map_mul,AlgHom.commutes,
    common_root,FifthBranchDifferential318.common_eq]
  exact (CharacterFifthCommonMultiple318.form_eq i).symm
end CharacterBranchLocalForm318
