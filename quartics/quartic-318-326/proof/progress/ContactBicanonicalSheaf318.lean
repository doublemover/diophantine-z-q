module
public import TensorOpenRestriction318
public import TensorSheafFunctor318
public import ContactIntrinsicFrames318
public section
noncomputable section
namespace ContactBicanonicalSheaf318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The genuine tensor square of the actual universal cotangent sheaf. -/
@[expose] def bicanonical : (ContactGlobalSmooth318.Model c).Modules :=
  IntrinsicTensorSheaf318.tensor (ContactIntrinsicDifferentials318.omega c)
    (ContactIntrinsicDifferentials318.omega c)

/-- New continuation: local frames on the checked five-chart cover, not a global trivialization. -/
@[expose] def localFrame (i : Option (Fin 4)) :
    (bicanonical c).restrict (ContactIntrinsicFrames318.embedding c i) ≅
      SheafOfModules.unit (ContactIntrinsicFrames318.chart c i).ringCatSheaf :=
  TensorOpenRestriction318.iso (ContactIntrinsicFrames318.embedding c i)
    (ContactIntrinsicDifferentials318.omega c) (ContactIntrinsicDifferentials318.omega c) ≪≫
      TensorSheafFunctor318.congr (ContactIntrinsicFrames318.localFrame c i)
        (ContactIntrinsicFrames318.localFrame c i) ≪≫ TensorSheafFunctor318.unitIso
end ContactBicanonicalSheaf318
