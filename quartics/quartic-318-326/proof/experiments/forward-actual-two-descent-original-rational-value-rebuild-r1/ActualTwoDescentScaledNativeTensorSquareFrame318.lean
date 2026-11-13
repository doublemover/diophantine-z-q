module
public import ActualTwoDescentOriginalIdealTensorInverse318
public import TensorSheafNormalization318
public section
noncomputable section
namespace ActualTwoDescentScaledNativeTensorSquareFrame318
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)

def squareFrame : (IntrinsicTensorSheaf318.tensor M M).restrict j ≅
    SheafOfModules.unit Y.ringCatSheaf :=
  TensorOpenRestriction318.iso j M M ≪≫ TensorSheafFunctor318.congr e e ≪≫
    TensorSheafFunctor318.unitIso

/-- The ACTUAL sheaf tensor,not tilde of an algebraic tensor by fiat,
has exact coefficient multiplication on every open of the original chart. -/
lemma squareFrame_pure (U : Y.Opens) (m n : Γ(M,j ''ᵁ U)) :
    (squareFrame j M e).hom.app U (IntrinsicTensorSheaf318.pure M M (j ''ᵁ U) m n)=
      e.hom.app U m*e.hom.app U n := by
  change TensorSheafFunctor318.unitIso.hom.app U
    ((TensorSheafFunctor318.congr e e).hom.app U
      ((TensorOpenRestriction318.iso j M M).hom.app U
        (IntrinsicTensorSheaf318.pure M M (j ''ᵁ U) m n)))=_
  rw [TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.congr_pure,TensorSheafNormalization318.unitIso_pure]

def scaledSquareFrame (a : Γ(Y,⊤)) (ha : IsUnit a) :
    (IntrinsicTensorSheaf318.tensor M M).restrict j ≅ SheafOfModules.unit Y.ringCatSheaf := by
  letI := ClutchedModule318.multiply_isIso a ha
  exact squareFrame j M e ≪≫ asIso (ClutchedModule318.multiply a)

lemma scaledSquareFrame_pure (a : Γ(Y,⊤)) (ha : IsUnit a)
    (U : Y.Opens) (m n : Γ(M,j ''ᵁ U)) :
    (scaledSquareFrame j M e a ha).hom.app U
      (IntrinsicTensorSheaf318.pure M M (j ''ᵁ U) m n)=
    (e.hom.app U m*e.hom.app U n)*
      (Y.presheaf.map (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op a) := by
  change (ClutchedModule318.multiply a).app U
    ((squareFrame j M e).hom.app U (IntrinsicTensorSheaf318.pure M M (j ''ᵁ U) m n))=_
  rw [squareFrame_pure,ClutchedModule318.multiply_apply]
end ActualTwoDescentScaledNativeTensorSquareFrame318
