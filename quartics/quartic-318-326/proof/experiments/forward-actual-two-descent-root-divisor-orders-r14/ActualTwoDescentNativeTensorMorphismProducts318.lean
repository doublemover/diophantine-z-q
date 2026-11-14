module
public import ActualTwoDescentOriginalIdealOverlapValues318
public section
noncomputable section
namespace ActualTwoDescentNativeTensorMorphismProducts318
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
local instance presheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))

def map {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q) :
    IntrinsicTensorSheaf318.tensor M N ⟶ IntrinsicTensorSheaf318.tensor P Q :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
    (f.val ⊗ₘ g.val)

lemma map_pure {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (U : X.Opens) (s : Γ(M,U)) (t : Γ(N,U)) :
    (map f g).app U (IntrinsicTensorSheaf318.pure M N U s t)=
      IntrinsicTensorSheaf318.pure P Q U (f.app U s) (g.app U t) :=
  congrArg (fun k => k.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (TensorSheafNormalization318.unit_map (f.val ⊗ₘ g.val))

def product {M N : X.Modules} (f : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (g : N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    IntrinsicTensorSheaf318.tensor M N ⟶ SheafOfModules.unit X.ringCatSheaf :=
  map f g ≫ TensorSheafFunctor318.unitIso.hom

lemma product_pure {M N : X.Modules} (f : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (g : N ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) :
    (product f g).app U (IntrinsicTensorSheaf318.pure M N U s t)=f.app U s*g.app U t := by
  change TensorSheafFunctor318.unitIso.hom.app U ((map f g).app U _)=_
  rw [map_pure,TensorSheafNormalization318.unitIso_pure]

/-- Extensionality for the native SHEAF tensor uses every subopen
and all pure tensors before sheafification,not just global sections. -/
lemma hom_ext_pure {M N P : X.Modules} (f g : IntrinsicTensorSheaf318.tensor M N ⟶ P)
    (h : ∀ U (s : Γ(M,U)) (t : Γ(N,U)),
      f.app U (IntrinsicTensorSheaf318.pure M N U s t)=
        g.app U (IntrinsicTensorSheaf318.pure M N U s t)) : f=g := by
  apply IntrinsicTensorSheaf318.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | zero => simp only [map_zero]
  | tmul s t => exact h U.unop s t
  | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy
end ActualTwoDescentNativeTensorMorphismProducts318
