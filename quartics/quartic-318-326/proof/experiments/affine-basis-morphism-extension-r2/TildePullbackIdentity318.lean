module
public import TildePullbackComposition318
public section
noncomputable section
namespace TildePullbackIdentity318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

lemma congr_mate {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackCongr h).hom =
        (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  ext M U
  simp

variable (R : CommRingCat.{u})

@[expose] def pullbackId : Scheme.Modules.pullback (Spec.map (𝟙 R)) ≅ 𝟭 (Spec R).Modules :=
  Scheme.Modules.pullbackCongr (Spec.map_id R) ≪≫ Scheme.Modules.pullbackId (Spec R)

lemma pullbackId_mate :
    conjugateEquiv Adjunction.id
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R)))
      (pullbackId R).hom = (AffineGlobalSectionCoherence318.specId R).inv := by
  change conjugateEquiv _ _
    ((Scheme.Modules.pullbackCongr (Spec.map_id R)).hom ≫
      (Scheme.Modules.pullbackId (Spec R)).hom) = _
  rw [← conjugateEquiv_comp _
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec R))),
    Scheme.Modules.conjugateEquiv_pullbackId_hom, congr_mate]
  rfl

lemma scalarId_mate :
    conjugateEquiv Adjunction.id (ModuleCat.extendRestrictScalarsAdj (RingHom.id R))
      (ModuleCat.extendScalarsId R).hom = (ModuleCat.restrictScalarsId R).inv := by
  simp only [ModuleCat.extendScalarsId, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Equiv.apply_symm_apply]

@[expose] def direct : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (𝟙 R)) ⟶
    tilde.functor R :=
  (TildePullback318.pullbackIso (𝟙 R)).hom ≫
    Functor.whiskerRight (ModuleCat.extendScalarsId R).hom (tilde.functor R) ≫
    (Functor.leftUnitor (tilde.functor R)).hom

@[expose] def original : tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (𝟙 R)) ⟶
    tilde.functor R :=
  Functor.whiskerLeft (tilde.functor R) (pullbackId R).hom ≫
    (Functor.rightUnitor (tilde.functor R)).hom

lemma direct_mate :
    conjugateEquiv (tilde.adjunction (R := R))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R)))) (direct R) =
    (Functor.rightUnitor moduleSpecΓFunctor).inv ≫
      Functor.whiskerLeft moduleSpecΓFunctor (ModuleCat.restrictScalarsId R).inv ≫
      (TildePullback318.globalNatIso (𝟙 R)).inv := by
  unfold direct
  rw [← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj (RingHom.id R)).comp (tilde.adjunction (R := R))),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (tilde.adjunction (R := R))),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight, scalarId_mate,
    TildePullbackMate318.comparison_mate]
  simp only [Category.assoc]

lemma original_mate :
    conjugateEquiv (tilde.adjunction (R := R))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R)))) (original R) =
    (Functor.leftUnitor moduleSpecΓFunctor).inv ≫
      Functor.whiskerRight (AffineGlobalSectionCoherence318.specId R).inv
        moduleSpecΓFunctor := by
  unfold original
  rw [← conjugateEquiv_comp _ ((tilde.adjunction (R := R)).comp Adjunction.id),
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft, pullbackId_mate]

/-- Canonical tilde pullback respects the actual identity comparison,
including the original Spec identity transport and module identity map. -/
lemma identity : direct R = original R := by
  apply (conjugateEquiv (tilde.adjunction (R := R))
      ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 R))))).injective
  rw [direct_mate, original_mate]
  apply NatTrans.ext
  funext M
  have h : moduleSpecΓFunctor.mapIso ((AffineGlobalSectionCoherence318.specId R).app M) =
      (TildePullback318.globalNatIso (𝟙 R)).app M ≪≫
        (ModuleCat.restrictScalarsId R).app (moduleSpecΓFunctor.obj M) :=
    Iso.ext (AffineGlobalSectionCoherence318.identity R M)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Iso.trans_inv, Functor.mapIso_inv] using (congrArg Iso.inv h).symm

lemma identity_app (M : ModuleCat R) :
    (TildePullback318.pullbackIso (𝟙 R)).hom.app M ≫
      (tilde.functor R).map ((ModuleCat.extendScalarsId R).hom.app M) =
        (pullbackId R).hom.app (tilde (R := R) M) := by
  simpa only [Functor.comp_obj, tilde.functor_obj, direct, original, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Category.comp_id] using congrArg (fun t => t.app M) (identity R)
end TildePullbackIdentity318
