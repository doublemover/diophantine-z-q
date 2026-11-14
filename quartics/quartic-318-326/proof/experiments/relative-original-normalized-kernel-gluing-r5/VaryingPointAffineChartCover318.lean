module
public import VaryingPointChartFreeness318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace VaryingPointAffineChartCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S)
abbrev pulledCover := (VaryingWordChartGluing318.cover R A ι).pullback₁ x.val
/-- Entire actual affine refinement of the pulled-back word-chart cover.
Its coefficient rings cover Spec S even when no global free frame exists. -/
@[expose] def cover : (Spec (CommRingCat.of S)).AffineOpenCover :=
  (pulledCover R A ι S x).affineRefinement
abbrev index := (cover R A ι S x).I₀
variable (i : index R A ι S x)
abbrev ring : CommRingCat.{u} := (cover R A ι S x).X i
@[expose] instance algebra : Algebra R (ring R A ι S x i) :=
  (((Spec.preimage ((cover R A ι S x).f i)).hom).comp (algebraMap R S)).toAlgebra
@[expose] def coefficient : S →ₐ[R] ring R A ι S x i where
  __ := (Spec.preimage ((cover R A ι S x).f i)).hom
  commutes' _ := rfl
lemma coefficient_spec : VaryingSourceCoefficientPullback318.coefficientChange R S
    (ring R A ι S x i) (coefficient R A ι S x i)=(cover R A ι S x).f i :=
  Spec.map_preimage _
abbrev word : ι → List A := i.1
@[expose] def chartMap : Spec (ring R A ι S x i) ⟶
    Spec (CommRingCat.of (VaryingNormalizedWordParameter318.ring R A ι (word R A ι S x i))) :=
  ((pulledCover R A ι S x).X i.1).affineOpenCover.f i.2 ≫
    pullback.snd x.val (VaryingWordChartGluing318.into R A ι i.1)
lemma chart_square : (VaryingParameterPoint318.map R A ι S (ring R A ι S x i)
    (coefficient R A ι S x i) x).val=
    chartMap R A ι S x i ≫ VaryingWordChartGluing318.into R A ι (word R A ι S x i) := by
  change VaryingSourceCoefficientPullback318.coefficientChange R S _ _ ≫ x.val=_
  rw [coefficient_spec]
  change (((pulledCover R A ι S x).X i.1).affineOpenCover.f i.2 ≫
    pullback.fst x.val (VaryingWordChartGluing318.into R A ι i.1)) ≫ x.val=
    (((pulledCover R A ι S x).X i.1).affineOpenCover.f i.2 ≫
    pullback.snd x.val (VaryingWordChartGluing318.into R A ι i.1)) ≫ _
  rw [Category.assoc,Category.assoc,pullback.condition]
end VaryingPointAffineChartCover318
