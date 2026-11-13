module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace IntrinsicTensorSheaf318
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

@[expose] def presheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R:=X.presheaf) M.val N.val

@[expose] def tensor : X.Modules :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj (presheaf M N)

@[expose] def homEquiv (P : X.Modules) :
    (tensor M N ⟶ P) ≃ (presheaf M N ⟶ P.val) :=
  PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

@[expose] def unit : presheaf M N ⟶ (tensor M N).val := homEquiv M N (tensor M N) (𝟙 _)

@[expose] def pure (U : X.Opens) (m : Γ(M,U)) (n : Γ(N,U)) : Γ(tensor M N,U) :=
  (unit M N).app (op U) (m ⊗ₜ[Γ(X,U)] n)

theorem homEquiv_apply (P : X.Modules) (f : tensor M N ⟶ P) :
    homEquiv M N P f = unit M N ≫ f.val := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right (𝟙 (tensor M N)) f
  change unit M N ≫ f.val=homEquiv M N P (𝟙 _ ≫ f) at h
  simpa only [Category.id_comp] using h.symm

theorem hom_ext {P : X.Modules} (f g : tensor M N ⟶ P)
    (h : unit M N ≫ f.val=unit M N ≫ g.val) : f=g := by
  apply (homEquiv M N P).injective
  simpa only [homEquiv_apply] using h

theorem pure_restrict {U V : X.Opens} (i : V ⟶ U) (m : Γ(M,U)) (n : Γ(N,U)) :
    (tensor M N).presheaf.map i.op (pure M N U m n) =
      pure M N V (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  have h := PresheafOfModules.naturality_apply (unit M N) i.op (m ⊗ₜ[Γ(X,U)] n)
  exact h.symm
end IntrinsicTensorSheaf318
