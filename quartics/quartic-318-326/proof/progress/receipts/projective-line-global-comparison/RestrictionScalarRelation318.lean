module
public import LocalCoordinateRelation318
public import ModuleScalar318
public section
noncomputable section
namespace RestrictionScalarRelation318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedModule318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {M : X.Modules} (f₀ f₁ : unit X ⟶ M) (a : Γ(Y,⊤))
/-- A literal ambient coordinate relation implies the exact relation of
restricted sheaf morphisms on the entire chart. -/
theorem relation
    (h : M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f₁.app ⊤ (show Γ(X,⊤) from 1))=
      (j.appIso ⊤).inv a • M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (f₀.app ⊤ (show Γ(X,⊤) from 1))) :
    (Scheme.Modules.restrictFunctor j).map f₁=
      (Scheme.Modules.restrictFunctor j).map f₀ ≫ ModuleScalar318.map (M.restrict j) a := by
  apply (cancel_epi (Scheme.Modules.restrictUnitIso j).inv).mp
  change LocalCoordinateRelation318.localMap j f₁=
    LocalCoordinateRelation318.localMap j f₀ ≫ ModuleScalar318.map (M.restrict j) a
  apply ModuleTopExt318.ext
  change (LocalCoordinateRelation318.localMap j f₁).app ⊤ (show Γ(Y,⊤) from 1)=
    (ModuleScalar318.map (M.restrict j) a).app ⊤
      ((LocalCoordinateRelation318.localMap j f₀).app ⊤ (show Γ(Y,⊤) from 1))
  rw [LocalCoordinateRelation318.localMap_top_one,ModuleScalar318.map_apply,
    LocalCoordinateRelation318.localMap_top_one]
  change M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
      (f₁.app ⊤ (show Γ(X,⊤) from 1))=
    (j.appIso ⊤).inv (Y.presheaf.map (𝟙 (op ⊤)) a) •
      M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
        (f₀.app ⊤ (show Γ(X,⊤) from 1))
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]
  exact h

/-- Reading the full-chart scalar relation at one yields its literal ambient coefficient. -/
theorem top_value
    (h : (Scheme.Modules.restrictFunctor j).map f₁=
      (Scheme.Modules.restrictFunctor j).map f₀ ≫ ModuleScalar318.map (M.restrict j) a) :
    f₁.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1)=
      (j.appIso ⊤).inv a • f₀.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1) := by
  have hh := congrArg (fun q : (unit X).restrict j ⟶ M.restrict j =>
    q.app ⊤ (show Γ(X,j ''ᵁ ⊤) from 1)) h
  change f₁.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1)=
    (ModuleScalar318.map (M.restrict j) a).app ⊤
      (f₀.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1)) at hh
  rw [ModuleScalar318.map_apply] at hh
  change f₁.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1)=
    (j.appIso ⊤).inv (Y.presheaf.map (𝟙 (op ⊤)) a) •
      f₀.app (j ''ᵁ ⊤) (show Γ(X,j ''ᵁ ⊤) from 1) at hh
  simpa only [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply] using hh
end RestrictionScalarRelation318
