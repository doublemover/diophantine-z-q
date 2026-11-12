module
public import TensorOpenRestriction318
public import TensorSheafFunctor318
public section
noncomputable section
namespace TensorSheafNormalization318
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}}
local instance presheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))

/-- The exact naturality identity for the actual module sheafification unit. -/
theorem unit_map {P Q : X.PresheafOfModules} (f : P ⟶ Q) :
    OpenSheafification318.unit P ≫
      ((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).map f).val =
      f ≫ OpenSheafification318.unit Q :=
  (PresheafOfModules.sheafificationAdjunction (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).unit_naturality f

theorem unit_counit (M : X.Modules) :
    OpenSheafification318.unit M.val ≫ (TensorSheafFunctor318.sheafifyIso M).hom.val = 𝟙 M.val :=
  (PresheafOfModules.sheafificationAdjunction (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).right_triangle_components M

theorem unit_comp (P : X.PresheafOfModules) (M : X.Modules)
    (f : OpenSheafification318.sheafify P ⟶ M) :
    OpenSheafification318.unit P ≫ f.val =
      PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj) f := by
  have h := (PresheafOfModules.sheafificationAdjunction (R:=X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right (𝟙 (OpenSheafification318.sheafify P)) f
  change OpenSheafification318.unit P ≫ f.val =
    PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj) (𝟙 _ ≫ f) at h
  simpa only [Category.id_comp] using h

/-- Exact normalization of the tensor functor on pure tensors. -/
theorem congr_pure {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N')
    (U : X.Opens) (m : Γ(M,U)) (n : Γ(N,U)) :
    (TensorSheafFunctor318.congr e f).hom.app U (IntrinsicTensorSheaf318.pure M N U m n) =
      IntrinsicTensorSheaf318.pure M' N' U (e.hom.app U m) (f.hom.app U n) := by
  let g := (tensorIso ((Scheme.Modules.toPresheafOfModules X).mapIso e)
    ((Scheme.Modules.toPresheafOfModules X).mapIso f)).hom
  exact congrArg (fun k => k.app (op U) (m ⊗ₜ[Γ(X,U)] n)) (unit_map g)

/-- The tensor-unit isomorphism has the actual multiplication normalization. -/
theorem unitIso_pure (U : X.Opens) (a b : Γ(X,U)) :
    (TensorSheafFunctor318.unitIso (X:=X)).hom.app U
      (IntrinsicTensorSheaf318.pure (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf) U a b) = a*b := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : IntrinsicTensorSheaf318.presheaf O O ⟶ O.val :=
    (λ_ (PresheafOfModulesOfCommRing.unit X.presheaf)).hom
  have h1 := congrArg (fun k => k.app (op U) (a ⊗ₜ[Γ(X,U)] b)) (unit_map g)
  have h2 := congrArg (fun k => k.app (op U) (a*b)) (unit_counit O)
  change (TensorSheafFunctor318.sheafifyIso O).hom.val.app (op U)
    (((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map g).val.app (op U)
      ((OpenSheafification318.unit (IntrinsicTensorSheaf318.presheaf O O)).app (op U)
        (a ⊗ₜ[Γ(X,U)] b))) = _
  change ((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map g).val.app (op U)
      ((OpenSheafification318.unit (IntrinsicTensorSheaf318.presheaf O O)).app (op U)
        (a ⊗ₜ[Γ(X,U)] b)) =
      (OpenSheafification318.unit O.val).app (op U) (a*b) at h1
  rw [h1]
  exact h2

variable {Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

theorem comparison_unit (P : Y.PresheafOfModules) :
    OpenSheafification318.unit ((OpenSheafification318.restriction j).obj P) ≫
      (OpenSheafification318.comparison j P).val =
        (OpenSheafification318.restriction j).map (OpenSheafification318.unit P) := by
  rw [unit_comp]
  exact Equiv.apply_symm_apply _ _

theorem comparison_inv_unit (P : Y.PresheafOfModules) :
    (OpenSheafification318.restriction j).map (OpenSheafification318.unit P) ≫
      (OpenSheafification318.iso j P).inv.val =
        OpenSheafification318.unit ((OpenSheafification318.restriction j).obj P) := by
  rw [←comparison_unit]
  change (OpenSheafification318.unit ((OpenSheafification318.restriction j).obj P) ≫
    (OpenSheafification318.iso j P).hom.val) ≫
      (OpenSheafification318.iso j P).inv.val = _
  rw [Category.assoc,←SheafOfModules.comp_val,Iso.hom_inv_id]
  rfl

/-- Restricting the genuine tensor sheaf sends the ambient pure tensor to
exactly the tensor of the two restricted sections, with no scalar factor. -/
theorem restriction_pure (M N : Y.Modules) (U : X.Opens)
    (m : Γ(M,j.opensFunctor.obj U)) (n : Γ(N,j.opensFunctor.obj U)) :
    (TensorOpenRestriction318.iso j M N).hom.app U
      (IntrinsicTensorSheaf318.pure M N (j.opensFunctor.obj U) m n) =
      IntrinsicTensorSheaf318.pure (M.restrict j) (N.restrict j) U m n := by
  let P := IntrinsicTensorSheaf318.presheaf M N
  let z := m ⊗ₜ[Γ(Y,j.opensFunctor.obj U)] n
  have h := congrArg (fun f => f.app (op U) z) (comparison_inv_unit j P)
  have h2 := congrArg (fun f => f.app (op U) z)
    (unit_map (TensorOpenRestriction318.presheafIso j M N).hom)
  change ((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map
      (TensorOpenRestriction318.presheafIso j M N).hom).val.app (op U)
    ((OpenSheafification318.iso j P).inv.val.app (op U)
      (((OpenSheafification318.restriction j).map (OpenSheafification318.unit P)).app (op U) z)) = _
  exact (congrArg (fun v =>
    ((PresheafOfModules.sheafification (R:=X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map
      (TensorOpenRestriction318.presheafIso j M N).hom).val.app (op U) v) h).trans h2
end TensorSheafNormalization318
