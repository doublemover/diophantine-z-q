module
public import OriginalLineAutomorphismScalar318
public import ModuleScalar318
public import Mathlib.CategoryTheory.Endomorphism
public section
noncomputable section
namespace OriginalLineAutomorphismEquiv318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open OriginalLineAutomorphismScalar318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}}

/-- The earlier original scalar-multiplication map, retained unchanged. -/
@[expose] def multiply (M : X.Modules) (a : Γ(X,⊤)) : M ⟶ M :=
  ModuleScalar318.map M a

lemma multiply_apply (M : X.Modules) (a : Γ(X,⊤)) (W : X.Opens) (s : Γ(M,W)) :
    (multiply M a).app W s =
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a • s :=
  ModuleScalar318.map_apply M a W s

/-- An actual global unit supplies an actual original module-sheaf
automorphism, with inverse multiplication by its actual inverse unit. -/
@[expose] def scalarIso (M : X.Modules) (a : Γ(X,⊤)ˣ) : M ≅ M where
  hom := multiply M a.val
  inv := multiply M a.inv
  hom_inv_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a.inv •
      (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a.val • s) = s
    rw [smul_smul, ← map_mul, a.inv_val, map_one, one_smul]
  inv_hom_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a.val •
      (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a.inv • s) = s
    rw [smul_smul, ← map_mul, a.val_inv, map_one, one_smul]

/-- The actual automorphism group of any original locally framed line
sheaf is exactly the actual group of global invertible regular functions. -/
@[expose] def equivalence (L : Line X) : Aut L.object ≃* Γ(X,⊤)ˣ where
  toFun f := scalar L f.asIso
  invFun a := Aut.of (scalarIso L.object a)
  left_inv f := by
    apply Aut.ext
    apply Iso.ext
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    exact (scalar_action L f.asIso W s).symm
  right_inv a := scalar_unique L (scalarIso L.object a) a (fun _ _ => rfl)
  map_mul' f g := by
    apply scalar_unique
    intro W s
    change f.asIso.hom.app W (g.asIso.hom.app W s) =
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        ((scalar L f.asIso).val * (scalar L g.asIso).val) • s
    rw [scalar_action L f.asIso, scalar_action L g.asIso, map_mul, smul_smul]
end OriginalLineAutomorphismEquiv318
