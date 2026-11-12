module
public import ModuleScalar318
public section
noncomputable section
namespace ModuleScalarComposition318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules)

lemma map_one : ModuleScalar318.map M 1=𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  change (ModuleScalar318.map M 1).app V s=s
  rw [ModuleScalar318.map_apply,map_one,one_smul]

lemma map_mul (r s : Γ(X,⊤)) :
    ModuleScalar318.map M (r*s)=ModuleScalar318.map M r ≫ ModuleScalar318.map M s := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  change (ModuleScalar318.map M (r*s)).app V x=
    (ModuleScalar318.map M s).app V ((ModuleScalar318.map M r).app V x)
  rw [ModuleScalar318.map_apply,ModuleScalar318.map_apply,ModuleScalar318.map_apply]
  rw [map_mul,←mul_smul,mul_comm]

/-- Every actual global unit gives an automorphism of the whole original
module sheaf, with its literal inverse scalar map. -/
@[expose] def unitIso (r : Γ(X,⊤)ˣ) : M ≅ M where
  hom := ModuleScalar318.map M (r:Γ(X,⊤))
  inv := ModuleScalar318.map M ((r⁻¹:Γ(X,⊤)ˣ):Γ(X,⊤))
  hom_inv_id := by rw [←map_mul,r.val_inv,map_one]
  inv_hom_id := by rw [←map_mul,r.inv_val,map_one]
end ModuleScalarComposition318
