module
public import RelativeCartierAffineBaseScheme318
public section
noncomputable section
namespace ClosedFamilyBaseSquare318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B T R V : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) (f : T ⟶ B) (u : R ⟶ B) (l : V ⟶ T) (k : V ⟶ R)
  (h : l ≫ f=k ≫ u)
local notation "P₀" => ClosedFamilyBaseRestriction318.into a p u
local notation "a₀" => pullback.snd a u
local notation "P₁" => ClosedFamilyIteratedCartesian318.into p a f l
local notation "v" => pullback.snd (pullback.snd a f) l
local notation "o" => ClosedFamilyIteratedCartesian318.original a f l
local notation "t" => ClosedFamilyIteratedCartesian318.toFamily p a f l
include h in
lemma ambient_outer : IsPullback o v a (k ≫ u) := by
  rw [← h]
  exact ClosedFamilyIteratedCartesian318.ambient_cartesian a f l
/-- Actual ambient map across a commuting coefficient square. -/
@[expose] def ambientMap : ClosedFamilyIteratedCartesian318.ambient a f l ⟶ pullback a u :=
  PullbackIntermediateFactor318.lift o v a k u (ambient_outer a f u l k h)
    (pullback.fst a u) a₀ (IsPullback.of_hasPullback a u)
@[reassoc] lemma ambient_original : ambientMap a f u l k h ≫ pullback.fst a u=o :=
  PullbackIntermediateFactor318.lift_left _ _ _ _ _ _ _ _ _
@[reassoc] lemma ambient_base : ambientMap a f u l k h ≫ a₀=v ≫ k :=
  PullbackIntermediateFactor318.lift_right _ _ _ _ _ _ _ _ _
lemma ambient_cartesian : IsPullback (ambientMap a f u l k h) v a₀ k :=
  PullbackIntermediateFactor318.cartesian _ _ _ _ _ _ _ _ _
include h in
lemma family_outer : IsPullback t (P₁ ≫ v) (p ≫ a) (k ≫ u) :=
  (ClosedFamilyIteratedCartesian318.family_cartesian p a f l).paste_vert
    (ambient_outer a f u l k h)
/-- Actual complete closed-family map over that ambient map, through the
full base-change universal property, retaining all nilpotents. -/
@[expose] def familyMap : ClosedFamilyIteratedCartesian318.family p a f l ⟶
    ClosedFamilyBaseRestriction318.family a p u :=
  PullbackIntermediateFactor318.lift t (P₁ ≫ v) (p ≫ a) k u (family_outer p a f u l k h)
    (pullback.fst (p ≫ a) u) (pullback.snd (p ≫ a) u) (IsPullback.of_hasPullback (p ≫ a) u)
@[reassoc] lemma family_original : familyMap p a f u l k h ≫
    ClosedFamilyBaseRestriction318.toFamily a p u=t :=
  PullbackIntermediateFactor318.lift_left _ _ _ _ _ _ _ _ _
@[reassoc] lemma family_base : familyMap p a f u l k h ≫
    ClosedFamilyBaseRestriction318.projection a p u=(P₁ ≫ v) ≫ k :=
  PullbackIntermediateFactor318.lift_right _ _ _ _ _ _ _ _ _
lemma family_base_cartesian : IsPullback (familyMap p a f u l k h) (P₁ ≫ v)
    (ClosedFamilyBaseRestriction318.projection a p u) k :=
  PullbackIntermediateFactor318.cartesian _ _ _ _ _ _ _ _ _
@[reassoc] lemma family_source : familyMap p a f u l k h ≫ P₀=P₁ ≫ ambientMap a f u l k h := by
  apply pullback.hom_ext
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_fst,← Category.assoc,
      family_original,Category.assoc,ambient_original]
    exact (ClosedFamilyIteratedCartesian318.family_cartesian p a f l).w
  · rw [Category.assoc,ClosedFamilyBaseRestriction318.into_snd,family_base,
      Category.assoc,ambient_base,Category.assoc]
lemma family_cartesian : IsPullback (familyMap p a f u l k h) P₁ P₀ (ambientMap a f u l k h) := by
  apply IsPullback.of_bot (v₂₁ := v) (v₂₂ := a₀)
  · simpa only [ClosedFamilyBaseRestriction318.into_snd] using family_base_cartesian p a f u l k h
  · exact family_source p a f u l k h
  · exact ambient_cartesian a f u l k h
end ClosedFamilyBaseSquare318
