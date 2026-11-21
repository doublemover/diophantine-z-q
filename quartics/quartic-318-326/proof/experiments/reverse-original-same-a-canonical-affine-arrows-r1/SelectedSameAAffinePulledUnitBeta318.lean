module

public import PulledCoordinateMaps318
public import ModuleTopExt318
public import TildeComparison318
public import InvariantTransition318
public import PullbackScalar318

/-!
# Pull the actual unit-section morphism through affine scalar extension

The canonical pullback of the section associated to m is the section
associated to 1 tensor m. The unit is the true structure sheaf map.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace SelectedSameAAffinePulledUnitBeta318

universe u
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {S T : CommRingCat.{u}} (r : S ⟶ T)
variable (M : ModuleCat S)


/-- The actual tilde comparison, transposed, has the expected global
normalization through true affine pushforward. -/
theorem adjoint_at_tilde (m : M) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map r)).homEquiv _ _ ((TildePullback318.pullbackIso r).hom.app M)).app ⊤
        ((tilde.isoTop (R := S) M).hom m) =
      (tilde.isoTop (R := T) ((ModuleCat.extendScalars r.hom).obj M)).hom ((1 : T) ⊗ₜ[S, r.hom] m) := by
  have hh := TildeComparison318.global_composite r M ((ModuleCat.extendScalars r.hom).obj M) (𝟙 ((ModuleCat.extendScalars r.hom).obj M))
  simp only [Functor.map_id, Category.comp_id] at hh
  rw [Adjunction.homEquiv_unit] at hh
  have hv := congrArg (fun q => q m) hh
  change (PushforwardGlobalSections318.globalIso r (tilde (R := T) ((ModuleCat.extendScalars r.hom).obj M))).hom
    (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map r)).homEquiv _ _ ((TildePullback318.pullbackIso r).hom.app M)).app ⊤
      ((tilde.isoTop (R := S) M).hom m)) = _
    at hv
  rw [InvariantTransition318.globalIso_apply] at hv
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hv
  exact hv

/-- This compares the actual pulled sheaf-module map with the honest
module scalar-extension section, not an arbitrarily rescaled value. -/
theorem pull_ofTop (m : M) :
    PulledCoordinateMaps318.map (Spec.map r)
        (ModuleGlobalSections318.ofTop (tilde (R := S) M)
          ((tilde.isoTop (R := S) M).hom m)) ≫ ((TildePullback318.pullbackIso r).hom.app M) =
      ModuleGlobalSections318.ofTop (tilde (R := T) ((ModuleCat.extendScalars r.hom).obj M))
        ((tilde.isoTop (R := T) ((ModuleCat.extendScalars r.hom).obj M)).hom ((1 : T) ⊗ₜ[S, r.hom] m)) := by
  let a := ModuleGlobalSections318.ofTop (tilde (R := S) M)
    ((tilde.isoTop (R := S) M).hom m)
  let b := ModuleGlobalSections318.ofTop (tilde (R := T) ((ModuleCat.extendScalars r.hom).obj M))
    ((tilde.isoTop (R := T) ((ModuleCat.extendScalars r.hom).obj M)).hom ((1 : T) ⊗ₜ[S, r.hom] m))
  change PulledCoordinateMaps318.map (Spec.map r) a ≫ ((TildePullback318.pullbackIso r).hom.app M) = b
  apply (cancel_epi (IdentityCotangent318.pullbackUnitIso (Spec.map r)).hom).mp
  simp only [PulledCoordinateMaps318.map, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map r)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    PullbackScalar318.adjoint_unit]
  apply ModuleTopExt318.ext
  change ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map r)).homEquiv _ _ ((TildePullback318.pullbackIso r).hom.app M)).app ⊤
    (a.app ⊤ (show Γ(Spec S, ⊤) from 1)) = b.app ⊤ ((Spec.map r).appTop 1)
  rw [map_one]
  unfold a b
  rw [ModuleTopMorphisms318.ofTop_top_one, ModuleTopMorphisms318.ofTop_top_one]
  exact adjoint_at_tilde r M m

end SelectedSameAAffinePulledUnitBeta318
