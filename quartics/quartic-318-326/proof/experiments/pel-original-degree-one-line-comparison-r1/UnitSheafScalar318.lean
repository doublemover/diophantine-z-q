module
public import ClutchedModule318
public import UnitModuleScalar318
public section
noncomputable section
namespace UnitSheafScalar318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}}
/-- Every actual endomorphism of O is multiplication by its original
value at one on the entire top open. -/
lemma hom_eq (f:ClutchedModule318.unit X⟶ClutchedModule318.unit X):
    f=ClutchedModule318.multiply (f.app ⊤ (1:Γ(X,⊤))):=by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have hn:=congrArg (fun g=>g (1:Γ(X,⊤)))
    (f.mapPresheaf.naturality (homOfLE (show U≤⊤ from le_top)).op)
  have h1:f.app U (1:Γ(X,U))=X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (f.app ⊤ (1:Γ(X,⊤))):=by
    change f.app U (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (1:Γ(X,⊤)))=
      X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (f.app ⊤ (1:Γ(X,⊤))) at hn
    simpa only [map_one] using hn
  change f.app U s=(ClutchedModule318.multiply (f.app ⊤ (1:Γ(X,⊤)))).app U s
  rw [ClutchedModule318.multiply_apply,←h1]
  simpa only [smul_eq_mul,mul_one] using f.app_smul s (1:Γ(X,U))
/-- The exact global unit of a unit-sheaf automorphism; its inverse is the
value of the inverse sheaf morphism, not just a nonvanishing scalar. -/
@[expose] def unit (e:ClutchedModule318.unit X≅ClutchedModule318.unit X):Γ(X,⊤)ˣ:=
  UnitModuleScalar318.unit
    (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv)
lemma unit_value (e:ClutchedModule318.unit X≅ClutchedModule318.unit X):
    (unit e).val=e.hom.app ⊤ (1:Γ(X,⊤)):=rfl
lemma hom_multiply (e:ClutchedModule318.unit X≅ClutchedModule318.unit X):
    e.hom=ClutchedModule318.multiply (unit e).val:=hom_eq e.hom
lemma inv_multiply (e:ClutchedModule318.unit X≅ClutchedModule318.unit X):
    e.inv=ClutchedModule318.multiply (unit e).inv:=hom_eq e.inv
lemma unique (e:ClutchedModule318.unit X≅ClutchedModule318.unit X) (a:Γ(X,⊤)ˣ)
    (h:e.hom=ClutchedModule318.multiply a.val):unit e=a:=by
  apply Units.ext
  change e.hom.app ⊤ (1:Γ(X,⊤))=a.val
  rw [h,ClutchedModule318.multiply_top,one_mul]
end UnitSheafScalar318
