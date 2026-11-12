module
public import RelativeAffineTestRule318
public section
noncomputable section
namespace RelativeAffineTestCover318
open AlgebraicGeometry CategoryTheory
open RelativeAffineTestRule318
universe u
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
@[expose] def cover (p : X ⟶ Spec (CommRingCat.of R)) : X.AffineOpenCover := X.affineOpenCover
abbrev index := (cover R p).I₀
variable (i : index R p)
abbrev ring : CommRingCat.{u} := (cover R p).X i
@[expose] instance algebra : Algebra R (ring R p i) :=
  (Spec.preimage ((cover R p).f i ≫ p)).hom.toAlgebra
lemma over : (cover R p).f i ≫ p=VaryingSourceCoefficientPullback318.base R (ring R p i) := by
  change (cover R p).f i ≫ p=Spec.map (Spec.preimage ((cover R p).f i ≫ p))
  exact (Spec.map_preimage _).symm
@[expose] def point : Test R p (ring R p i) := ⟨(cover R p).f i,over R p i⟩
end RelativeAffineTestCover318
