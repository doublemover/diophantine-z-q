module
public import CanonicalStalkModule318
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Data.Complex.Basic
public section
noncomputable section
namespace CanonicalComplexStalkScalars318
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
/-- The actual structural pullback on global scalars. -/
@[expose] def globalBase : ℂ →+* Γ(X,⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
/-- The actual structural scalars followed by the original ring germ. -/
@[expose] def stalkBase (x : X) : ℂ →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom.comp (globalBase f)
@[expose] def globalAlgebra : Algebra ℂ Γ(X,⊤) := (globalBase f).toAlgebra
@[expose] def stalkAlgebra (x : X) : Algebra ℂ (X.presheaf.stalk x) := (stalkBase f x).toAlgebra
@[expose] def sectionModule (M : X.Modules) : Module ℂ Γ(M,⊤) :=
  Module.compHom Γ(M,⊤) (globalBase f)
@[expose] def stalkModule (M : X.Modules) (x : X) : Module ℂ (CanonicalStalkModule318.stalk M x) :=
  Module.compHom (CanonicalStalkModule318.stalk M x) (stalkBase f x)
@[expose] def stalkTower (M : X.Modules) (x : X) :
    letI := stalkAlgebra f x
    letI := stalkModule f M x
    IsScalarTower ℂ (X.presheaf.stalk x) (CanonicalStalkModule318.stalk M x) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
/-- Actual section germs are linear for the actual structural complex
scalars. No scalar action is transported through a chosen equivalence. -/
@[expose] def germ (M : X.Modules) (x : X) :
    letI := sectionModule f M
    letI := stalkModule f M x
    Γ(M,⊤) →ₗ[ℂ] CanonicalStalkModule318.stalk M x := {
  __ := (M.presheaf.germ ⊤ x trivial).hom
  map_smul' c s := by
    change M.presheaf.germ ⊤ x trivial (globalBase f c • s) =
      X.presheaf.germ ⊤ x trivial (globalBase f c) • M.presheaf.germ ⊤ x trivial s
    exact PresheafOfModules.germ_smul M.val x ⊤ trivial _ _ }
end CanonicalComplexStalkScalars318
