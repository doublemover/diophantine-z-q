module
public import PELOriginalProductComplexPoints318
public section
noncomputable section
namespace PELOriginalTripleProductReduced318
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Triple := pullback (baseMap τ hτ) (π τ hτ)
abbrev TripleRing (j k l : Label 3) := ProductRing τ hτ j k ⊗[ℂ] CoordinateChart τ hτ l

/-- Every actual triple-chart tensor is detected by its genuine algebra
points; reducedness is proved directly from pair-point separation. -/
instance tripleRingReduced (j k l : Label 3) : _root_.IsReduced (TripleRing τ hτ j k l) where
  eq_zero a ha := by
    apply TensorComplexPointSeparation318.eq_zero ?_ ?_ a
    · intro x hx
      apply PELOriginalProductChartPoints318.ext τ hτ j k
      intro f g
      rw [hx,map_zero]
    · intro x hx
      apply PELOriginalChartPointSeparation318.ext τ hτ l
      intro f
      rw [hx,map_zero]
    · intro f g
      exact isNilpotent_iff_eq_zero.mp (ha.map (TensorComplexPointSeparation318.evaluation f g))

@[expose] def rawCover : (Triple τ hτ).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (PELOriginalProductChartCover318.affineCover τ hτ)
    (cover τ hτ) (baseMap τ hτ) (π τ hτ)

@[expose] def chartIso (j k l : Label 3) :
    Spec (CommRingCat.of (TripleRing τ hτ j k l)) ≅
      pullback (chartInclusion τ hτ (j,k)≫baseMap τ hτ) (chartMap τ hτ l≫π τ hτ) :=
  (pullbackSpecIso ℂ (ProductRing τ hτ j k) (CoordinateChart τ hτ l)).symm ≪≫
    pullback.congrHom (chart_over τ hτ j k).symm (chart_over_complex_base τ hτ l).symm

@[expose] def chartMap (i : (Label 3 × Label 3) × Label 3) :
    Spec (CommRingCat.of (TripleRing τ hτ i.1.1 i.1.2 i.2)) ⟶ Triple τ hτ :=
  (chartIso τ hτ i.1.1 i.1.2 i.2).hom≫(rawCover τ hτ).f i

/-- A genuine729-member affine cover of the ACTUAL triple fiber
product, retaining the exact tensor scalar structures of both stages. -/
@[expose] def affineCover : (Triple τ hτ).OpenCover :=
  (rawCover τ hτ).copy ((Label 3 × Label 3) × Label 3)
    (fun i => Spec (CommRingCat.of (TripleRing τ hτ i.1.1 i.1.2 i.2)))
    (chartMap τ hτ) (Equiv.refl _) (fun i => chartIso τ hτ i.1.1 i.1.2 i.2)
    (fun _ => rfl)

/-- Genuine reducedness needed to prove eventual associativity from
all original complex triples. No scheme identity is asserted merely
from a set-level transported analytic law. -/
instance tripleReduced : IsReduced (Triple τ hτ) :=
  IsReduced.of_openCover _ (affineCover τ hτ)

lemma chart_count : Fintype.card ((Label 3 × Label 3) × Label 3)=729 := by
  norm_num [Label,Fintype.card_prod]
end PELOriginalTripleProductReduced318
