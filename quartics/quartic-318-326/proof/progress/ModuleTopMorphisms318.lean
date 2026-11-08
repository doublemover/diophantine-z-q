module
public import ModuleGlobalSections318
public section
noncomputable section
namespace ModuleTopMorphisms318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

theorem ofTop_top_one (s : Γ(M,⊤)) :
    (ModuleGlobalSections318.ofTop M s).val.app (op ⊤) (show Γ(X,⊤) from 1)=s := by
  have h := ModuleGlobalSections318.ofTop_one M s ⊤
  simpa only [show (homOfLE (show (⊤:X.Opens) ≤ ⊤ from le_top)).op=𝟙 (op ⊤) from rfl,
    CategoryTheory.Functor.map_id,ConcreteCategory.id_apply] using h

/-- The section-to-morphism correspondence commutes with an actual sheaf map. -/
theorem ofTop_comp (s : Γ(M,⊤)) (f : M ⟶ N) :
    ModuleGlobalSections318.ofTop M s≫f=
      ModuleGlobalSections318.ofTop N (f.app ⊤ s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change f.app U ((ModuleGlobalSections318.ofTop M s).val.app (op U) (show Γ(X,U) from a))=
    (ModuleGlobalSections318.ofTop N (f.app ⊤ s)).val.app (op U) (show Γ(X,U) from a)
  rw [ModuleGlobalSections318.ofTop_apply,Scheme.Modules.Hom.app_smul,
    ModuleGlobalSections318.ofTop_apply]
  congr 1
  exact congrArg (fun g => g s) (f.mapPresheaf.naturality
    (homOfLE (show U≤⊤ from le_top)).op)
end ModuleTopMorphisms318
