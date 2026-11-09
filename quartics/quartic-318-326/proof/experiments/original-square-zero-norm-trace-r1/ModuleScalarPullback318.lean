module
public import ModuleScalar318
public import UnitSheafScalar318
public section
noncomputable section
namespace ModuleScalarPullback318
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}}
lemma map_one (M : X.Modules) : ModuleScalar318.map M 1 = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (X.presheaf.map (homOfLE le_top).op (1 : Γ(X,⊤))) • s = s
  rw [map_one, one_smul]
lemma map_mul (M : X.Modules) (a b : Γ(X,⊤)) :
    ModuleScalar318.map M a ≫ ModuleScalar318.map M b = ModuleScalar318.map M (a * b) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (X.presheaf.map (homOfLE le_top).op b) •
    ((X.presheaf.map (homOfLE le_top).op a) • s) =
      (X.presheaf.map (homOfLE le_top).op (a * b)) • s
  rw [map_mul, smul_smul, mul_comm]
/-- Every actual global unit acts by an actual module-sheaf automorphism. -/
@[expose] def unitIso (M : X.Modules) (a : Γ(X,⊤)ˣ) : M ≅ M where
  hom := ModuleScalar318.map M a.val
  inv := ModuleScalar318.map M a.inv
  hom_inv_id := by rw [map_mul, a.val_inv, map_one]
  inv_hom_id := by rw [map_mul, a.inv_val, map_one]
/-- Semilinearity of an ORIGINAL map into the actual direct image gives the
scalar square on every open, including the original coefficient restrictions. -/
lemma adjoint_scalar (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (q : M ⟶ (Scheme.Modules.pushforward f).obj N) (a : Γ(Y,⊤)) :
    ModuleScalar318.map M a ≫ q = q ≫
      (Scheme.Modules.pushforward f).map (ModuleScalar318.map N (f.appTop a)) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change q.app U ((Y.presheaf.map (homOfLE le_top).op a) • s) =
    (X.presheaf.map (homOfLE le_top).op (f.appTop a)) • q.app U s
  rw [Scheme.Modules.Hom.app_smul]
  change (f.app U (Y.presheaf.map (homOfLE le_top).op a)) • q.app U s = _
  congr 1
  exact congrArg (fun k => k a) (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
/-- Actual pullback of multiplication on ANY module, proved by the original
adjunction, not assumed from the scalar formula for the structure line alone. -/
lemma pullback_map (f : X ⟶ Y) (M : Y.Modules) (a : Γ(Y,⊤)) :
    (Scheme.Modules.pullback f).map (ModuleScalar318.map M a) =
      ModuleScalar318.map ((Scheme.Modules.pullback f).obj M) (f.appTop a) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hleft := adj.homEquiv_naturality_left (ModuleScalar318.map M a)
    (𝟙 ((Scheme.Modules.pullback f).obj M))
  have hright := adj.homEquiv_naturality_right
    (𝟙 ((Scheme.Modules.pullback f).obj M))
    (ModuleScalar318.map ((Scheme.Modules.pullback f).obj M) (f.appTop a))
  apply (adj.homEquiv _ _).injective
  simpa only [Category.comp_id, Category.id_comp] using
    hleft.trans ((adjoint_scalar f (adj.homEquiv _ _ (𝟙 _)) a).trans hright.symm)
end ModuleScalarPullback318
