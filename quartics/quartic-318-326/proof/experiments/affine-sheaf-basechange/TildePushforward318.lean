module
public import TildePullback318
public section
noncomputable section
namespace TildePushforward318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The actual affine pushforward of an original affine tilde model is
canonically tilde of its original scalar-restricted section module. -/
@[expose] def sectionsIso (M : (Spec S).Modules) [IsIso M.fromTildeΓ] :
    tilde ((ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj M)) ≅
      (Scheme.Modules.pushforward (Spec.map f)).obj M := by
  haveI := isIso_fromTildeΓ_pushforward f M
  exact (tilde.functor R).mapIso (PushforwardGlobalSections318.globalIso f M).symm ≪≫
    asIso ((Scheme.Modules.pushforward (Spec.map f)).obj M).fromTildeΓ

/-- The affine pushforward comparison for the unchanged tilde of any module. -/
@[expose] def component (N : ModuleCat.{u} S) :
    tilde ((ModuleCat.restrictScalars f.hom).obj N) ≅
      (Scheme.Modules.pushforward (Spec.map f)).obj (tilde N) :=
  (tilde.functor R).mapIso
    ((ModuleCat.restrictScalars f.hom).mapIso (tilde.toTildeΓNatIso.app N)) ≪≫
      sectionsIso f (tilde N)

lemma sectionsIso_hom (M : (Spec S).Modules) [IsIso M.fromTildeΓ] :
    (sectionsIso f M).hom =
      (tilde.functor R).map (PushforwardGlobalSections318.globalIso f M).inv ≫
        ((Scheme.Modules.pushforward (Spec.map f)).obj M).fromTildeΓ := rfl

lemma sectionsIso_naturality {M N : (Spec S).Modules}
    [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] (h : M ⟶ N) :
    (tilde.functor R).map ((ModuleCat.restrictScalars f.hom).map
        (moduleSpecΓFunctor.map h)) ≫ (sectionsIso f N).hom =
      (sectionsIso f M).hom ≫ (Scheme.Modules.pushforward (Spec.map f)).map h := by
  simp only [sectionsIso_hom, ← Category.assoc, ← Functor.map_comp]
  have hn : (ModuleCat.restrictScalars f.hom).map (moduleSpecΓFunctor.map h) ≫
      (PushforwardGlobalSections318.globalIso f N).inv =
    (PushforwardGlobalSections318.globalIso f M).inv ≫
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (Spec.map f)).map h) :=
    (TildePullback318.globalNatIso f).inv.naturality h
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun k => (tilde.functor R).map
    (PushforwardGlobalSections318.globalIso f M).inv ≫ k)
    (Scheme.Modules.fromTildeΓNatTrans.naturality
      ((Scheme.Modules.pushforward (Spec.map f)).map h))
end TildePushforward318
