module
public import OriginalOpenPullbackComposition318
public import RestrictionPullbackCoherence318
public section
noncomputable section
namespace RestrictionTransitionPasting318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
  [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]

@[expose] def collapse : Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor f ≅
    Scheme.Modules.restrictFunctor fg :=
  (Scheme.Modules.restrictFunctorComp f g).symm ≪≫ Scheme.Modules.restrictFunctorCongr h

/-- Normalize the actual restriction equality transport on reflexivity
by its original section maps; it is not definitionally eqToIso. -/
lemma restrictionCongr_refl (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app,eqToHom_refl,
    Opposite.op_id,CategoryTheory.Functor.map_id,Scheme.Modules.Hom.id_app] <;> rfl

/-- The original restriction-to-pullback comparison preserves named
composition paths, using the existing adjunction-normalized theorem. -/
lemma comparison_path (M : Z.Modules) :
    (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (PullbackPathComposition318.iso f g fg h).hom.app M =
    (collapse f g fg h).hom.app M ≫ (Scheme.Modules.restrictFunctorIsoPullback fg).hom.app M := by
  subst fg
  have hc := RestrictionPullbackCoherence318.composition f g M
  have hh : (Scheme.Modules.restrictFunctor f).map
      ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
          (Scheme.Modules.pullbackComp f g).hom.app M =
      (Scheme.Modules.restrictFunctorComp f g).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
    have hh := congrArg (fun q => (Scheme.Modules.restrictFunctorComp f g).inv.app M ≫
      q ≫ (Scheme.Modules.pullbackComp f g).hom.app M) hc
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hh.symm
  simpa only [collapse, PullbackPathComposition318.iso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.pullbackCongr, restrictionCongr_refl,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using hh

variable {M : Z.Modules} {N : Y.Modules} {Q : X.Modules}
  (t : (Scheme.Modules.pullback g).obj M ⟶ N)
  (s : (Scheme.Modules.pullback f).obj N ⟶ Q)
  (r : (Scheme.Modules.pullback fg).obj M ⟶ Q)

/-- A proved actual pullback transition equation gives the corresponding
actual restriction-functor equation, with no extra normalization premise. -/
lemma transition_pasting
    (ht : (Scheme.Modules.pullback f).map t ≫ s =
      (PullbackPathComposition318.iso f g fg h).hom.app M ≫ r) :
    (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M ≫ t) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N ≫ s =
    (collapse f g fg h).hom.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback fg).hom.app M ≫ r := by
  have hn := (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality t
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor f).map t), hn, Category.assoc, ht]
  simpa only [Category.assoc] using congrArg (fun q => q ≫ r) (comparison_path f g fg h M)
end RestrictionTransitionPasting318
