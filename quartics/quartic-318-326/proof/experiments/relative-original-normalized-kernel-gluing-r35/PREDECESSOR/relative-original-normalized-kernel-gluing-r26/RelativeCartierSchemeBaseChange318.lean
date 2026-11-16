module
public import ClosedFamilyBaseSquare318
public section
noncomputable section
namespace RelativeCartierSchemeBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B T : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) [hflat : Flat (p ≫ a)] (f : T ⟶ B)
include hflat in
/-- A genuine relative Cartier closed family, flat over its coefficient
base, remains genuinely Cartier after EVERY scheme coefficient change.
Neither base is required affine, reduced or flat over the other. -/
lemma regular (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property (ClosedFamilyBaseRestriction318.into a p f) := by
  let U := B.affineOpenCover
  let V := U.openCover.pullback₁ f
  apply RegularClosedBaseCover318.regular _ (pullback.snd a f) V
  intro i
  let R : CommRingCat := U.X i
  let u : Spec R ⟶ B := U.f i
  let l := pullback.fst f u
  let k := pullback.snd f u
  have hs : l ≫ f=k ≫ u := pullback.condition
  let P := ClosedFamilyBaseRestriction318.into a p u
  let b := pullback.snd a u
  have hP : OriginalRegularClosedCharts318.Property P :=
    RegularClosedFlatPullback318.regular p P
      (ClosedFamilyBaseRestriction318.toFamily a p u) (pullback.fst a u)
      (ClosedFamilyBaseRestriction318.cartesian a p u) h
  letI : Flat (P ≫ b) := by
    change Flat (ClosedFamilyBaseRestriction318.into a p u ≫ pullback.snd a u)
    rw [ClosedFamilyBaseRestriction318.into_snd]
    infer_instance
  have hnew := RelativeCartierAffineBaseScheme318.regular R P b k hP
  exact ClosedFamilyCartesianModel318.regular P b k
    (ClosedFamilyIteratedCartesian318.into p a f l)
    (ClosedFamilyBaseSquare318.familyMap p a f u l k hs)
    (ClosedFamilyBaseSquare318.ambientMap a f u l k hs)
    (pullback.snd (pullback.snd a f) l)
    (ClosedFamilyBaseSquare318.family_cartesian p a f u l k hs)
    (ClosedFamilyBaseSquare318.ambient_cartesian a f u l k hs) hnew
end RelativeCartierSchemeBaseChange318
