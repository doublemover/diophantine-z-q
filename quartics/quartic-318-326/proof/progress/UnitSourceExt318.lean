module
public import ModuleGlobalSections318
public section
noncomputable section
namespace UnitSourceExt318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules)
/-- A genuine morphism from O to the original module sheaf is determined
by its actual top-open section at one. -/
lemma eq_ofTop (f:SheafOfModules.unit X.ringCatSheaf⟶M):
    f=ModuleGlobalSections318.ofTop M ((Scheme.Modules.Hom.app f) ⊤ (1:Γ(X,⊤))):=by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have hn:=congrArg (fun g=>g (1:Γ(X,⊤)))
    ((Scheme.Modules.Hom.mapPresheaf f).naturality (homOfLE (show U≤⊤ from le_top)).op)
  have h1:(Scheme.Modules.Hom.app f) U (1:Γ(X,U))=M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op
      ((Scheme.Modules.Hom.app f) ⊤ (1:Γ(X,⊤))):=by
    change (Scheme.Modules.Hom.app f) U (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (1:Γ(X,⊤)))=
      M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op ((Scheme.Modules.Hom.app f) ⊤ (1:Γ(X,⊤))) at hn
    simpa only [map_one] using hn
  let s':Γ(X,U):=s
  have h2:(Scheme.Modules.Hom.app f) U s'=s' • (Scheme.Modules.Hom.app f) U (1:Γ(X,U)):=by
    simpa only [smul_eq_mul,mul_one] using Scheme.Modules.Hom.app_smul f s' (1:Γ(X,U))
  have h3:=ModuleGlobalSections318.ofTop_apply M
    ((Scheme.Modules.Hom.app f) ⊤ (1:Γ(X,⊤))) U s'
  exact h2.trans ((congrArg (fun t:Γ(M,U)=>s' • t) h1).trans h3.symm)

lemma ext (f g:SheafOfModules.unit X.ringCatSheaf⟶M)
    (h:(Scheme.Modules.Hom.app f) ⊤ (1:Γ(X,⊤))=(Scheme.Modules.Hom.app g) ⊤ (1:Γ(X,⊤))):f=g:=by
  exact (eq_ofTop M f).trans ((congrArg (ModuleGlobalSections318.ofTop M) h).trans (eq_ofTop M g).symm)
end UnitSourceExt318
