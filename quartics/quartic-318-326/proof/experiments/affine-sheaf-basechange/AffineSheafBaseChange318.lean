module
public import TildePushforward318
public import AffineModuleMate318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace AffineSheafBaseChange318
open CategoryTheory AlgebraicGeometry AffineModuleBaseChange318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
abbrev baseMapA : R ⟶ A := CommRingCat.ofHom (algebraMap R A)
abbrev baseMapB : R ⟶ B := CommRingCat.ofHom (algebraMap R B)

/-- The literal tensor ring yields the actual scheme fiber square. -/
lemma isPullback : IsPullback (Spec.map (leftMap R A B))
    (Spec.map (rightMap R A B)) (Spec.map (baseMapA R A))
      (Spec.map (baseMapB R B)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R A B)

/-- Actual affine scheme pull-push comparison on the literal tensor
pushout, for every original module sheaf with invertible tilde-Gamma counit.
Its middle module comparison is the actual extension/restriction mate. -/
@[expose] def iso (M : (Spec B).Modules) [IsIso M.fromTildeΓ] :
    (Scheme.Modules.pullback (Spec.map (baseMapA R A))).obj
      ((Scheme.Modules.pushforward (Spec.map (baseMapB R B))).obj M) ≅
    (Scheme.Modules.pushforward (Spec.map (leftMap R A B))).obj
      ((Scheme.Modules.pullback (Spec.map (rightMap R A B))).obj M) :=
  (Scheme.Modules.pullback (Spec.map (baseMapA R A))).mapIso
      (TildePushforward318.sectionsIso (baseMapB R B) M).symm ≪≫
    (TildePullback318.pullbackIso (baseMapA R A)).app _ ≪≫
    (tilde.functor A).mapIso (component R A B (moduleSpecΓFunctor.obj M)).symm ≪≫
    TildePushforward318.component (leftMap R A B) _ ≪≫
    (Scheme.Modules.pushforward (Spec.map (leftMap R A B))).mapIso
      ((TildePullback318.pullbackIso (rightMap R A B)).app _).symm ≪≫
    (Scheme.Modules.pushforward (Spec.map (leftMap R A B))).mapIso
      ((Scheme.Modules.pullback (Spec.map (rightMap R A B))).mapIso (asIso M.fromTildeΓ))

/-- The module factor in the comparison is literally the canonical mate,
with its original restriction square and adjunction units. -/
lemma module_factor (M : (Spec B).Modules) :
    (tilde.functor A).map (component R A B (moduleSpecΓFunctor.obj M)).inv =
      (tilde.functor A).map
        (AffineModuleMate318.baseChangeMap R A B (moduleSpecΓFunctor.obj M)) := by
  rw [AffineModuleMate318.baseChangeMap_eq]
end AffineSheafBaseChange318
