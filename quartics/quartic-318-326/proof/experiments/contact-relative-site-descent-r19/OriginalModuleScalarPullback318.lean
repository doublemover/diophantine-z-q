module
public import ModuleScalar318
public section
noncomputable section
namespace OriginalModuleScalarPullback318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- Original pushforward scalar multiplication uses the original structural
section map, on every open. -/
lemma pushforward_scalar (N : X.Modules) (a : Γ(Y,⊤)) :
    (Scheme.Modules.pushforward p).map (ModuleScalar318.map N (p.appTop a)) =
      ModuleScalar318.map ((Scheme.Modules.pushforward p).obj N) a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change Γ(N, p ⁻¹ᵁ U) at s
  change X.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op (p.appTop a) • s =
    p.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) • s
  congr 1
  exact (congrArg (fun f => f a) (p.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)).symm

/-- Actual module-sheaf pullback preserves scalar multiplication through
the original appTop map. No flatness or local-freeness hypothesis is needed. -/
lemma pullback_scalar (M : Y.Modules) (a : Γ(Y,⊤)) :
    (Scheme.Modules.pullback p).map (ModuleScalar318.map M a) =
      ModuleScalar318.map ((Scheme.Modules.pullback p).obj M) (p.appTop a) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction p
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [pushforward_scalar]
  exact (adj.unit.naturality (ModuleScalar318.map M a)).symm.trans
    (ModuleScalar318.natural a (adj.unit.app M))
end OriginalModuleScalarPullback318
