module
public import ClutchedModule318
public import ModuleTopExt318
public section
noncomputable section
namespace StructureLineAutomorphisms318
open AlgebraicGeometry CategoryTheory
universe u
variable (X : Scheme.{u})
local notation "O" => SheafOfModules.unit X.ringCatSheaf

lemma apply_scalar (f : O ⟶ O) (a : Γ(X,⊤)) :
    f.app ⊤ a=a * f.app ⊤ 1 := by
  calc
    f.app ⊤ a=(ModuleGlobalSections318.ofTop O (f.app ⊤ 1)).app ⊤ a :=
      congrArg (fun q => q.app ⊤ a) (ModuleTopExt318.eq_ofTop f)
    _ = a * f.app ⊤ 1 := ClutchedModule318.multiply_top _ _

/-- An automorphism of the actual structure line supplies an ACTUAL
unit global function, with its inverse given by the inverse sheaf map. -/
@[expose] def value (e : O ≅ O) : Γ(X,⊤)ˣ where
  val := e.hom.app ⊤ 1
  inv := e.inv.app ⊤ 1
  val_inv := by
    have h := congrArg (fun f => f.app ⊤ (show Γ(X,⊤) from 1)) e.hom_inv_id
    change e.inv.app ⊤ (e.hom.app ⊤ 1)=1 at h
    rw [apply_scalar] at h
    exact h
  inv_val := by
    have h := congrArg (fun f => f.app ⊤ (show Γ(X,⊤) from 1)) e.inv_hom_id
    change e.hom.app ⊤ (e.inv.app ⊤ 1)=1 at h
    rw [apply_scalar] at h
    exact h

@[expose] def iso (u : Γ(X,⊤)ˣ) : O ≅ O := by
  letI := ClutchedModule318.multiply_isIso (u:Γ(X,⊤)) u.isUnit
  exact asIso (ClutchedModule318.multiply (u:Γ(X,⊤)))

lemma iso_value (u : Γ(X,⊤)ˣ) : value X (iso X u)=u := by
  apply Units.ext
  exact (ClutchedModule318.multiply_top (u:Γ(X,⊤)) 1).trans (one_mul _)

lemma value_iso (e : O ≅ O) : iso X (value X e)=e := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  exact (ClutchedModule318.multiply_top (value X e : Γ(X,⊤)) 1).trans (one_mul _)

/-- Genuine structure-sheaf automorphisms are exactly units of the full
original global-function ring, on arbitrary schemes. -/
@[expose] def equivalence : (O ≅ O) ≃ Γ(X,⊤)ˣ where
  toFun := value X
  invFun := iso X
  left_inv := value_iso X
  right_inv := iso_value X
end StructureLineAutomorphisms318
