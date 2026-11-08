module
public import ModuleTopMorphisms318
public section
noncomputable section
namespace ModuleTopExt318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
abbrev unit (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
variable {X : Scheme.{u}} {M : X.Modules}
/-- A morphism from the structure sheaf is determined by its global value at one. -/
theorem eq_ofTop (f : unit X ⟶ M) :
    f=ModuleGlobalSections318.ofTop M (f.app ⊤ (show Γ(X,⊤) from 1)) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change f.app U (show Γ(X,U) from a)=
    (ModuleGlobalSections318.ofTop M _).val.app (op U) (show Γ(X,U) from a)
  rw [ModuleGlobalSections318.ofTop_apply]
  have hn := congrArg (fun g => g (show Γ(X,⊤) from 1))
    (f.mapPresheaf.naturality (homOfLE (show U≤⊤ from le_top)).op)
  change f.app U (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op 1)=
    M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (f.app ⊤ (show Γ(X,⊤) from 1)) at hn
  rw [map_one] at hn
  rw [←hn]
  have hm := Scheme.Modules.Hom.app_smul f (show Γ(X,U) from a) (show Γ(X,U) from 1)
  simpa only [smul_eq_mul,mul_one] using hm

theorem ext {f g : unit X ⟶ M}
    (h : f.app ⊤ (show Γ(X,⊤) from 1)=g.app ⊤ (show Γ(X,⊤) from 1)) : f=g :=
  (eq_ofTop f).trans ((congrArg (ModuleGlobalSections318.ofTop M) h).trans (eq_ofTop g).symm)
end ModuleTopExt318
