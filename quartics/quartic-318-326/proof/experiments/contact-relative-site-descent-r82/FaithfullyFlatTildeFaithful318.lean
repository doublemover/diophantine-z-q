module
public import GeometricAffineDescentData318
public section
noncomputable section
namespace FaithfullyFlatTildeFaithful318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]

/-- Original scalar extension reflects module maps by the actual
faithfully flat comparison equivalence. -/
lemma scalar_map_injective {M N : ModuleCat.{u} R} (h k : M ⟶ N)
    (hh : (ModuleCat.extendScalars (algebraMap R S)).map h =
      (ModuleCat.extendScalars (algebraMap R S)).map k) : h = k := by
  let F := Comonad.comparison (AffineCoalgebraModule318.adjunction (algebraMap R S))
  letI : F.IsEquivalence := (comonadicExtendScalars
    (AffineCoalgebraLine318.faithfullyFlat R S)).eqv
  apply F.map_injective
  apply Comonad.Coalgebra.Hom.ext
  exact hh

/-- Actual sheaf pullback reflects every morphism between affine tilde
objects. No pointwise test or faithfulness assumption is introduced. -/
lemma pullback_map_injective {M N : ModuleCat.{u} R}
    (h k : (tilde.functor R).obj M ⟶ (tilde.functor R).obj N)
    (hh : (Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map h =
      (Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map k) : h = k := by
  let F := tilde.functor R
  let h' := F.preimage h
  let k' := F.preimage k
  have he : F.map h' = h := F.map_preimage h
  have ke : F.map k' = k := F.map_preimage k
  suffices h' = k' by rw [← he, ← ke, this]
  apply scalar_map_injective R S
  apply (tilde.functor S).map_injective
  let a := (TildePullback318.pullbackIso (AffineCoalgebraLine318.ringMap R S)).hom
  apply (cancel_epi (a.app M)).mp
  have hn := congrArg (fun t => t ≫ a.app N) hh
  rw [← he, ← ke] at hn
  change (F ⋙ Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map h' ≫
    a.app N = (F ⋙ Scheme.Modules.pullback (Spec.map (AffineCoalgebraLine318.ringMap R S))).map k' ≫
    a.app N at hn
  rw [a.naturality h', a.naturality k'] at hn
  exact hn
end FaithfullyFlatTildeFaithful318
