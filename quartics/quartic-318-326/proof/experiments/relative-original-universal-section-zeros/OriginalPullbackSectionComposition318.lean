module
public import OriginalOpenPullbackSections318
public import SchemeIsoPushforwardRecovery318
public section
noncomputable section
namespace OriginalPullbackSectionComposition318
open AlgebraicGeometry CategoryTheory
open OriginalOpenPullbackSections318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The original geometric unit is natural in the original module map. -/
lemma naturality {M N : Y.Modules} (q : M ⟶ N) (s : Γ(M,⊤)) :
    ((Scheme.Modules.pullback f).map q).app ⊤ (sectionPull f M s) =
      sectionPull f N (q.app ⊤ s) := by
  have h := congrArg (fun t => t.app ⊤ s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality q)
  exact h.symm

/-- Composition of the actual two geometric units, with the unchanged
pullback associator. This follows from its defining mate, not an extra law. -/
lemma composition (M : Z.Modules) (s : Γ(M,⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
      (sectionPull f ((Scheme.Modules.pullback g).obj M) (sectionPull g M s)) =
        sectionPull (f ≫ g) M s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv,Adjunction.comp_unit_app] at h
  have he := congrArg (fun t => t.app ⊤ s) h
  change sectionPull f ((Scheme.Modules.pullback g).obj M) (sectionPull g M s) =
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤
      (sectionPull (f ≫ g) M s) at he
  rw [he]
  exact ConcreteCategory.congr_hom
    (congrArg (fun t => t.app ⊤) ((Scheme.Modules.pullbackComp f g).app M).inv_hom_id) _

/-- The same original unit equation along a specified actual path. -/
lemma path (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules) (s : Γ(M,⊤)) :
    ((PullbackPathComposition318.iso f g k h).hom.app M).app ⊤
      (sectionPull f ((Scheme.Modules.pullback g).obj M) (sectionPull g M s)) =
        sectionPull k M s := by
  subst k
  simpa only [PullbackPathComposition318.iso,Iso.trans_hom,NatTrans.comp_app,
    Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app,
    Category.comp_id] using composition f g M s

/-- Recovery along the actual scheme isomorphism is the inverse of the
original geometric unit, not merely some section-space equivalence. -/
lemma recovery_unit [IsIso f] (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (SchemeIsoPushforwardRecovery318.recovery f M).hom = 𝟙 M := by
  have h := OriginalOpenLineRestrictionUnit318.restriction_unit f M
  let e := asIso ((Scheme.Modules.restrictAdjunction f).unit.app M) ≪≫
    (Scheme.Modules.pushforward f).mapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M)
  have he : e.hom = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := h
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫ e.inv = 𝟙 M
  rw [← he]
  exact e.hom_inv_id

lemma recovery_apply [IsIso f] (M : Y.Modules) (s : Γ(M,⊤)) :
    (SchemeIsoPushforwardRecovery318.recovery f M).hom.app ⊤ (sectionPull f M s) = s :=
  ConcreteCategory.congr_hom (congrArg (fun t => t.app ⊤) (recovery_unit f M)) s
end OriginalPullbackSectionComposition318
