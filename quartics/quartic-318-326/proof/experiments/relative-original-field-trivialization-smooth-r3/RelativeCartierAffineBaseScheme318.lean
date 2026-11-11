module
public import ClosedFamilyIteratedCartesian318
public section
noncomputable section
namespace RelativeCartierAffineBaseScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u}) {Z X T : Scheme.{u}}
  (p : Z ⟶ X) [IsClosedImmersion p] (a : X ⟶ Spec R)
  [hflat : Flat (p ≫ a)] (f : T ⟶ Spec R)
include hflat in
/-- Over an affine original coefficient base, genuine flat Cartier
families remain Cartier on EVERY new coefficient SCHEME. The whole
new affine cover is used, without assuming the new scheme is affine. -/
lemma regular (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property (ClosedFamilyBaseRestriction318.into a p f) := by
  apply RegularClosedBaseCover318.regular _ (pullback.snd a f) T.affineOpenCover.openCover
  intro i
  let S : CommRingCat := T.affineOpenCover.X i
  let k : Spec S ⟶ T := T.affineOpenCover.f i
  let φ : R ⟶ S := Spec.preimage (k ≫ f)
  letI : Algebra R S := φ.hom.toAlgebra
  have hf : RelativeOriginalAffineChart318.baseMap R S=k ≫ f := Spec.map_preimage _
  apply RelativeCartierAffineCartesian318.regular R S p a
    (ClosedFamilyIteratedCartesian318.into p a f k)
    (ClosedFamilyIteratedCartesian318.toFamily p a f k)
    (ClosedFamilyIteratedCartesian318.original a f k)
    (pullback.snd (pullback.snd a f) k)
  · exact ClosedFamilyIteratedCartesian318.family_cartesian p a f k
  · rw [hf]
    exact ClosedFamilyIteratedCartesian318.ambient_cartesian a f k
  · exact h
end RelativeCartierAffineBaseScheme318
