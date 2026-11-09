module
public import AffineComparisonMates318
public section
noncomputable section
namespace TildePullbackComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

/-- The path using the comparison for the composite map and then the
original canonical scalar-extension composition isomorphism. -/
@[expose] def direct :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (f ≫ g)) ⟶
      ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom ⋙ tilde.functor T :=
  (TildePullback318.pullbackIso (f ≫ g)).hom ≫
    Functor.whiskerRight (ModuleCat.extendScalarsComp f.hom g.hom).hom (tilde.functor T) ≫
    (Functor.associator _ _ _).hom

/-- The path using the original sheaf pullback composition isomorphism
and the two actual canonical tilde pullback comparisons. -/
@[expose] def iterated :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (f ≫ g)) ⟶
      ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom ⋙ tilde.functor T :=
  Functor.whiskerLeft (tilde.functor R) (AffineComparisonMates318.pullbackComp f g).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (TildePullback318.pullbackIso f).hom
      (Scheme.Modules.pullback (Spec.map g)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ModuleCat.extendScalars f.hom) (TildePullback318.pullbackIso g).hom

lemma direct_mate :
    conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T))))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g))))
      (direct f g) =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft moduleSpecΓFunctor
        (ModuleCat.restrictScalarsComp f.hom g.hom).inv ≫
      (TildePullback318.globalNatIso (f ≫ g)).inv := by
  unfold direct
  rw [← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp
        (tilde.adjunction (R := T))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        (ModuleCat.extendRestrictScalarsAdj g.hom)).comp (tilde.adjunction (R := T))),
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    AffineComparisonMates318.scalarComp_mate, TildePullbackMate318.comparison_mate]
  simp only [Category.assoc]

lemma associator_inverse_mate :
    conjugateEquiv
      (((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
      ((tilde.adjunction (R := R)).comp
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  have h : conjugateIsoEquiv
      ((tilde.adjunction (R := R)).comp
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))))
      (((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
      (Functor.associator _ _ _) = Functor.associator _ _ _ :=
    Iso.ext (conjugateEquiv_associator_hom _ _ _)
  exact congrArg Iso.inv h

lemma iterated_mate :
    conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T))))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g))))
      (iterated f g) =
    Functor.whiskerRight (TildePullback318.globalNatIso g).inv
        (ModuleCat.restrictScalars f.hom) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Scheme.Modules.pushforward (Spec.map g))
        (TildePullback318.globalNatIso f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (AffineGlobalSectionCoherence318.specComp f g).hom
        moduleSpecΓFunctor := by
  unfold iterated
  rw [← conjugateEquiv_comp _
      ((tilde.adjunction (R := R)).comp
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))),
    ← conjugateEquiv_comp _
      (((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        (tilde.adjunction (R := S))).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))),
    ← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        ((tilde.adjunction (R := S)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))),
    conjugateEquiv_whiskerLeft, TildePullbackMate318.comparison_mate,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    TildePullbackMate318.comparison_mate, associator_inverse_mate,
    conjugateEquiv_whiskerLeft, AffineComparisonMates318.pullbackComp_inverse_mate]
  simp only [Category.assoc]

/-- Exact composition coherence of the existing canonical affine
sheaf-to-module comparison. No cocycle or coherence premise is assumed. -/
lemma composition : direct f g = iterated f g := by
  apply (conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T))))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g))))).injective
  rw [direct_mate, iterated_mate]
  apply NatTrans.ext
  intro M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using
      AffineGlobalSectionCoherence318.inverse_composition f g M

lemma composition_app (M : ModuleCat R) :
    (TildePullback318.pullbackIso (f ≫ g)).hom.app M ≫
      (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M) =
    (AffineComparisonMates318.pullbackComp f g).inv.app (tilde M) ≫
      (Scheme.Modules.pullback (Spec.map g)).map ((TildePullback318.pullbackIso f).hom.app M) ≫
      (TildePullback318.pullbackIso g).hom.app ((ModuleCat.extendScalars f.hom).obj M) := by
  simpa only [Functor.comp_obj, tilde.functor_obj, direct, iterated, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using congrArg (fun t => t.app M) (composition f g)
end TildePullbackComposition318
