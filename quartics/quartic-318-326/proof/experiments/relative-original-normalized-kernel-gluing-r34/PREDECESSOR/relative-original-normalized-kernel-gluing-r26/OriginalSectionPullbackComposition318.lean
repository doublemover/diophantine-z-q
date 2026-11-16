module
public import OriginalOpenPullbackSections318
public import Mathlib.CategoryTheory.Adjunction.Mates
public section
noncomputable section
namespace OriginalSectionPullbackComposition318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- The geometric unit on entire sections for an arbitrary morphism,
including non-flat coefficient change. No open-immersion hypothesis. -/
@[expose] def pull (M : Y.Modules) : Γ(M,⊤) →+ Γ((Scheme.Modules.pullback f).obj M,⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom

lemma naturality {M N : Y.Modules} (a : M ⟶ N) (s : Γ(M,⊤)) :
    ((Scheme.Modules.pullback f).map a).app ⊤ (pull f M s) =
      pull f N (a.app ⊤ s) := by
  have h := congrArg (fun q => q.app ⊤ s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)
  exact h.symm

variable (g : Y ⟶ Z)
/-- Composition retains the genuine pullback associator and actual
adjunction units. It holds on every original section, not only frames. -/
lemma composition (M : Z.Modules) (s : Γ(M,⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
      (pull f ((Scheme.Modules.pullback g).obj M) (pull g M s)) =
        pull (f ≫ g) M s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hs := congrArg (fun q => q.app ⊤ s) h
  change pull f ((Scheme.Modules.pullback g).obj M) (pull g M s) =
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤ (pull (f ≫ g) M s) at hs
  rw [hs]
  exact congrArg (fun q => q.app ⊤ (pull (f ≫ g) M s))
    ((Scheme.Modules.pullbackComp f g).inv_hom_id_app M)

lemma path (h : X ⟶ Z) (hh : f ≫ g = h) (M : Z.Modules) (s : Γ(M,⊤)) :
    ((PullbackPathComposition318.iso f g h hh).hom.app M).app ⊤
      (pull f ((Scheme.Modules.pullback g).obj M) (pull g M s)) = pull h M s := by
  subst h
  simpa only [PullbackPathComposition318.iso,Scheme.Modules.pullbackCongr,
    eqToIso_refl,Iso.trans_hom,Iso.refl_hom,NatTrans.comp_app,NatTrans.id_app,Category.comp_id] using
      composition f g M s

variable {Y' : Scheme.{u}} (f' : X ⟶ Y') (g' : Y' ⟶ Z)
  (h : f ≫ g = f' ≫ g')
/-- A literal geometric square, with its original path comparison,
commutes on genuine pullback units. This is the normalization needed
before transporting the contact Cech restriction squares. -/
lemma square (M : Z.Modules) (s : Γ(M,⊤)) :
    (((Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp f' g').app M).symm).hom).app ⊤
        (pull f ((Scheme.Modules.pullback g).obj M) (pull g M s)) =
      pull f' ((Scheme.Modules.pullback g').obj M) (pull g' M s) := by
  have hp := path f g (f' ≫ g') h M s
  have hq := composition f' g' M s
  change ((Scheme.Modules.pullbackComp f' g').inv.app M).app ⊤
    (((PullbackPathComposition318.iso f g (f' ≫ g') h).hom.app M).app ⊤
      (pull f ((Scheme.Modules.pullback g).obj M) (pull g M s))) = _
  rw [hp,← hq]
  exact congrArg (fun q => q.app ⊤
    (pull f' ((Scheme.Modules.pullback g').obj M) (pull g' M s)))
      ((Scheme.Modules.pullbackComp f' g').hom_inv_id_app M)
end OriginalSectionPullbackComposition318
