module
public import ModuleGlobalSections318
public section
noncomputable section
namespace OpenPushforwardGlobalValue318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward j).obj N)

@[expose] def localMap : M.restrict j ⟶ N :=
  (Scheme.Modules.restrictFunctor j).map f ≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j).hom.app N

/-- Restriction followed by the actual open-immersion counit recovers the
literal global section on the chart. No unspecified scalar is introduced. -/
theorem localMap_top (s : Γ(M,⊤)) :
    (localMap j M N f).app ⊤
      (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)=f.app ⊤ s := by
  change N.presheaf.map (eqToHom (j.preimage_image_eq ⊤).symm).op
    (f.app (j ''ᵁ ⊤) (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s))=f.app ⊤ s
  have hn := congrArg (fun g => g s) (f.mapPresheaf.naturality
    (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op)
  change f.app (j ''ᵁ ⊤) (M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)=
    N.presheaf.map ((TopologicalSpace.Opens.map j.base).map
      (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top))).op (f.app ⊤ s) at hn
  rw [hn]
  change N.presheaf.map (eqToHom (j.preimage_image_eq ⊤).symm).op
    (N.presheaf.map ((TopologicalSpace.Opens.map j.base).map
      (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top))).op (f.app ⊤ s))=f.app ⊤ s
  rw [←CategoryTheory.Functor.map_comp_apply]
  change N.presheaf.map (𝟙 (op ⊤)) (f.app ⊤ s)=f.app ⊤ s
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]
end OpenPushforwardGlobalValue318
