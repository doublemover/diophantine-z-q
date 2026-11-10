module
public import OriginalOpenLineRestrictionUnit318
public import RestrictionPullbackCoherence318
public import OpenChartSections318
public import PullbackPathComposition318
public section
noncomputable section
namespace OriginalOpenPullbackSections318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Actual original pullback sections identify with sections of the SAME
original module on the FULL image open. -/
def sectionsEquiv (M : Y.Modules) :
    Γ((Scheme.Modules.pullback f).obj M,⊤) ≃+ Γ(M,f ''ᵁ ⊤) :=
  (((Scheme.Modules.toPresheaf X).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm)).app (op ⊤)).addCommGroupIsoToAddEquiv

/-- The original geometric section pullback, defined by its actual unit. -/
@[expose] def sectionPull (M : Y.Modules) : Γ(M,⊤) →+ Γ((Scheme.Modules.pullback f).obj M,⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom

/-- This is the original ambient presheaf restriction, not an unrelated map
of isomorphic section spaces. -/
lemma unit_sections (M : Y.Modules) (s : Γ(M,⊤)) :
    sectionsEquiv f M (sectionPull f M s) =
      M.presheaf.map (homOfLE (f.image_preimage_le ⊤)).op s := by
  have h := congrArg (fun q => q.app ⊤ s)
    (OriginalOpenLineRestrictionUnit318.restriction_unit_inverse f M)
  change ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ s) =
    ((Scheme.Modules.restrictAdjunction f).unit.app M).app ⊤ s at h
  exact h

variable (g : Y ⟶ Z) [IsOpenImmersion g]

/-- The inverse actual restriction/pullback composition comparison, with
all original maps retained. -/
lemma inverse_composition (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M =
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) ≫
      (Scheme.Modules.restrictFunctorComp f g).inv.app M := by
  let a := (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).app M
  let b := (Scheme.Modules.pullbackComp f g).app M
  let c := (Scheme.Modules.restrictFunctorComp f g).app M
  let d := (Scheme.Modules.restrictFunctor f).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app M)
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app ((Scheme.Modules.pullback g).obj M)
  have h : a ≪≫ b.symm = c ≪≫ d ≪≫ e :=
    Iso.ext (RestrictionPullbackCoherence318.composition f g M)
  simpa only [a,b,c,d,e,Iso.trans_inv,Iso.symm_inv,NatIso.app_hom,NatIso.app_inv,
    Functor.mapIso_inv,Category.assoc] using congrArg Iso.inv h

/-- Restriction through nested original charts agrees with the actual
whole-open presheaf restriction, retaining the original pullback associator. -/
lemma nested_sections (M : Z.Modules)
    (s : Γ((Scheme.Modules.pullback g).obj M,⊤)) :
    sectionsEquiv (f ≫ g) M
      (((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
        (sectionPull f ((Scheme.Modules.pullback g).obj M) s)) =
      M.presheaf.map (homOfLE (OpenChartSections318.imageLE f g)).op
        (sectionsEquiv g M s) := by
  have hc := congrArg (fun q => q.app ⊤
    (sectionPull f ((Scheme.Modules.pullback g).obj M) s)) (inverse_composition f g M)
  change sectionsEquiv (f ≫ g) M
      (((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
        (sectionPull f ((Scheme.Modules.pullback g).obj M) s)) =
    ((Scheme.Modules.restrictFunctorComp f g).inv.app M).app ⊤
      (((Scheme.Modules.restrictFunctor f).map
        ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M)).app ⊤
          (sectionsEquiv f ((Scheme.Modules.pullback g).obj M)
            (sectionPull f ((Scheme.Modules.pullback g).obj M) s))) at hc
  rw [hc,unit_sections]
  have hn := ((Scheme.Modules.toPresheaf Y).map
    ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M)).naturality
      (homOfLE (f.image_preimage_le ⊤)).op
  have hn' := ConcreteCategory.congr_hom hn s
  change ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M).app (f ''ᵁ ⊤)
      (((Scheme.Modules.pullback g).obj M).presheaf.map
        (homOfLE (f.image_preimage_le ⊤)).op s) =
    ((Scheme.Modules.restrictFunctor g).obj M).presheaf.map
      (homOfLE (f.image_preimage_le ⊤)).op (sectionsEquiv g M s) at hn'
  change ((Scheme.Modules.restrictFunctorComp f g).inv.app M).app ⊤
    (((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M).app (f ''ᵁ ⊤)
      (((Scheme.Modules.pullback g).obj M).presheaf.map
        (homOfLE (f.image_preimage_le ⊤)).op s)) = _
  rw [hn',Scheme.Modules.restrictFunctorComp_inv_app_app]
  change M.presheaf.map _ (M.presheaf.map _ (sectionsEquiv g M s)) =
    M.presheaf.map _ (sectionsEquiv g M s)
  rw [← Functor.map_comp_apply] <;> rfl
/-- The same formula along a proved literal composite path. No ambient
open is silently substituted; its inclusion is transported by that path. -/
lemma nested_path (k : X ⟶ Z) [IsOpenImmersion k] (h : f ≫ g = k)
    (M : Z.Modules) (s : Γ((Scheme.Modules.pullback g).obj M,⊤)) :
    sectionsEquiv k M
      (((PullbackPathComposition318.iso f g k h).hom.app M).app ⊤
        (sectionPull f ((Scheme.Modules.pullback g).obj M) s)) =
      M.presheaf.map (homOfLE (show k ''ᵁ ⊤ ≤ g ''ᵁ ⊤ by
        rw [← h]; exact OpenChartSections318.imageLE f g)).op
        (sectionsEquiv g M s) := by
  subst k
  simpa only [PullbackPathComposition318.iso,Iso.trans_hom,NatTrans.comp_app,
    Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app,
    Category.comp_id] using nested_sections f g M s
end OriginalOpenPullbackSections318
