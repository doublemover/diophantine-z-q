module
public import OriginalTensorRightUnit318
public import ModuleScalar318
public section
noncomputable section
namespace OriginalTensorFrameChange318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Equality on every original pure section on every open detects actual
maps out of the sheafified tensor product, by its original universal map. -/
lemma pure_ext {P : X.Modules} (f g : IntrinsicTensorSheaf318.tensor M N ⟶ P)
    (h : ∀ (U : X.Opens) (m : Γ(M,U)) (n : Γ(N,U)),
      f.app U (IntrinsicTensorSheaf318.pure M N U m n) =
        g.app U (IntrinsicTensorSheaf318.pure M N U m n)) : f = g := by
  apply IntrinsicTensorSheaf318.hom_ext M N
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => exact h U.unop m n
  | add x y hx hy => simpa only [map_add,hx,hy]

/-- Untwist using a specified actual frame on this scheme. -/
@[expose] def iso (e : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    IntrinsicTensorSheaf318.tensor M N ≅ M :=
  TensorSheafFunctor318.congr (Iso.refl M) e ≪≫ OriginalTensorRightUnit318.iso M

lemma pure (e : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (m : Γ(M,U)) (n : Γ(N,U)) :
    (iso M N e).hom.app U (IntrinsicTensorSheaf318.pure M N U m n) = (e.hom.app U n) • m := by
  change (OriginalTensorRightUnit318.iso M).hom.app U
    ((TensorSheafFunctor318.congr (Iso.refl M) e).hom.app U
      (IntrinsicTensorSheaf318.pure M N U m n)) = _
  rw [TensorSheafNormalization318.congr_pure]
  exact OriginalTensorRightUnit318.pure M U m (e.hom.app U n)

/-- Changing the genuine twist frame by a specified original global
regular scalar changes the ACTUAL tensor comparison by exactly that scalar
on the SAME original module. No coefficient or section action is replaced. -/
lemma scalar_change (e f : N ≅ SheafOfModules.unit X.ringCatSheaf) (a : Γ(X,⊤))
    (h : e.hom = f.hom ≫ ModuleScalar318.map (SheafOfModules.unit X.ringCatSheaf) a) :
    (iso M N e).hom = (iso M N f).hom ≫ ModuleScalar318.map M a := by
  apply pure_ext M N
  intro U m n
  have he := congrArg (fun q => q.app U n) h
  change (e.hom.app U n) =
    (ModuleScalar318.map (SheafOfModules.unit X.ringCatSheaf) a).app U (f.hom.app U n) at he
  change (iso M N e).hom.app U (IntrinsicTensorSheaf318.pure M N U m n) =
    (ModuleScalar318.map M a).app U
      ((iso M N f).hom.app U (IntrinsicTensorSheaf318.pure M N U m n))
  rw [pure,pure,he,ModuleScalar318.map_apply,ModuleScalar318.map_apply]
  change ((X.presheaf.map (homOfLE le_top).op a) * (f.hom.app U n)) • m =
    (X.presheaf.map (homOfLE le_top).op a) • ((f.hom.app U n) • m)
  exact mul_smul _ _ _
end OriginalTensorFrameChange318
