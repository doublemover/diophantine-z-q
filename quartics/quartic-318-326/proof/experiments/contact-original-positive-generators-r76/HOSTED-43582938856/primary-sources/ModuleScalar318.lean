module
public import ClutchedModule318
public section
noncomputable section
namespace ModuleScalar318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}}
/-- Multiplication by a global regular function on any actual module sheaf. -/
@[expose] def map (M : X.Modules) (a : Γ(X,⊤)) : M ⟶ M where
  val.app U := ModuleCat.ofHom
    ((X.presheaf.map (homOfLE (show U.unop≤⊤ from le_top)).op a) • (LinearMap.id : Γ(M,U.unop) →ₗ[Γ(X,U.unop)] Γ(M,U.unop)))
  val.naturality := by
    intro U V f
    obtain ⟨U,rfl⟩ := Opposite.op_surjective U
    obtain ⟨V,rfl⟩ := Opposite.op_surjective V
    ext s
    change Γ(M,U) at s
    symm
    change M.presheaf.map f
      ((X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a) • (show Γ(M,U) from s))=
      (X.presheaf.map (homOfLE (show V≤⊤ from le_top)).op a) • (show Γ(M,V) from M.presheaf.map f s)
    exact (Scheme.Modules.map_smul M f.unop
      (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a) s).trans
      (congrArg (fun r : Γ(X,V) => r • (show Γ(M,V) from M.presheaf.map f s))
        (CategoryTheory.Functor.map_comp_apply X.presheaf _ f a).symm)

theorem map_apply (M : X.Modules) (a : Γ(X,⊤)) (U : X.Opens) (s : Γ(M,U)) :
    (map M a).app U s=(X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a) • s := rfl

/-- Scalar multiplication commutes with every actual module-sheaf morphism. -/
theorem natural {M N : X.Modules} (a : Γ(X,⊤)) (f : M ⟶ N) :
    map M a ≫ f=f ≫ map N a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact Scheme.Modules.Hom.app_smul f _ _

theorem unit_eq (a : Γ(X,⊤)) : map (ClutchedModule318.unit X) a=ClutchedModule318.multiply a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op a) * (show Γ(X,U) from s)=
    (ClutchedModule318.multiply a).app U s
  rw [ClutchedModule318.multiply_apply,mul_comm]
end ModuleScalar318
