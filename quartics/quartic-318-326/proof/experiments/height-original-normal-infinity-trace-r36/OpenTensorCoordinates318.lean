module
public import TensorSheafNormalization318
public import OpenPushforwardGlobalValue318
public section
noncomputable section
namespace OpenTensorCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M N : X.Modules)
  (e : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
  (f : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)

/-- The actual tensor frame on an arbitrary open immersion, with its
original scalar comparison, not only on an open-subscheme inclusion. -/
@[expose] def frame : (tensor M N).restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  TensorOpenRestriction318.iso j M N ≪≫ TensorSheafFunctor318.congr e f ≪≫
    TensorSheafFunctor318.unitIso

lemma frame_pure (V : Y.Opens) (m : Γ(M,j ''ᵁ V)) (n : Γ(N,j ''ᵁ V)) :
    (frame j M N e f).hom.app V (pure M N (j ''ᵁ V) m n) =
      e.hom.app V m * f.hom.app V n := by
  change TensorSheafFunctor318.unitIso.hom.app V
    ((TensorSheafFunctor318.congr e f).hom.app V
      ((TensorOpenRestriction318.iso j M N).hom.app V
        (pure M N (j ''ᵁ V) m n))) = _
  rw [TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.congr_pure,TensorSheafNormalization318.unitIso_pure]

@[expose] def coordinate : tensor M N ⟶
    (Scheme.Modules.pushforward j).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction j).homEquiv _ _ (frame j M N e f).hom

lemma coordinate_pure (V : X.Opens) (m : Γ(M,V)) (n : Γ(N,V)) :
    (coordinate j M N e f).app V (pure M N V m n) =
      ((Scheme.Modules.restrictAdjunction j).homEquiv M _ e.hom).app V m *
      ((Scheme.Modules.restrictAdjunction j).homEquiv N _ f.hom).app V n := by
  change (frame j M N e f).hom.app (j ⁻¹ᵁ V)
    ((tensor M N).presheaf.map (homOfLE (j.image_preimage_le V)).op
      (pure M N V m n)) = _
  rw [pure_restrict,frame_pure]
  rfl

lemma transpose :
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).symm
      (coordinate j M N e f) = (frame j M N e f).hom :=
  Equiv.symm_apply_apply _ _

/-- Equality of actual sheaf tensor maps can be tested on pure tensors on
ALL opens, by the genuine sheafification adjunction and tensor induction. -/
theorem hom_ext {P : X.Modules} (a b : tensor M N ⟶ P)
    (h : ∀ V (m : Γ(M,V)) (n : Γ(N,V)),
      a.app V (pure M N V m n) = b.app V (pure M N V m n)) : a = b := by
  apply IntrinsicTensorSheaf318.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n => exact h V.unop m n
  | add z w hz hw => simpa only [map_add,hz,hw]
end OpenTensorCoordinates318
