module
public import ComplexProjectiveVariableCover318
public import PELOriginalCandidateChartFiniteType318
public section
noncomputable section
namespace PELOriginalCandidateNineChartCover318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateAffineCharts318
open PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)
lemma charts_cover(p:candidate τ hτ):∃j:Label 3,p∈candidateChart τ hτ j:=
  ComplexProjectiveVariableCover318.exists_variable_nonmem (inclusion τ hτ p)
@[expose] def chartMap(j:Label 3):Spec (CommRingCat.of (CoordinateChart τ hτ j))⟶candidate τ hτ:=
  (actualChartIso τ hτ j).hom≫(candidateChart τ hτ j).ι
instance chartMap_open(j:Label 3):IsOpenImmersion (chartMap τ hτ j):=by
  dsimp [chartMap]
  infer_instance

/-- A genuine NINE-member affine open cover of the SAME candidate,
using its literal degree-zero quotient coordinate rings and actual
original ambient coordinate opens. It covers ALL scheme primes. -/
@[expose] def cover:(candidate τ hτ).OpenCover where
  I₀:=Label 3
  X j:=Spec (CommRingCat.of (CoordinateChart τ hτ j))
  f:=chartMap τ hτ
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      obtain ⟨j,hj⟩:=charts_cover τ hτ p
      refine ⟨j,(actualChartIso τ hτ j).inv ⟨p,hj⟩,?_⟩
      exact congrArg (candidateChart τ hτ j).ι
        (Iso.inv_hom_id_apply (actualChartIso τ hτ j) ⟨p,hj⟩)
    · intro j
      infer_instance
lemma cover_size:Fintype.card (Label 3)=9:=by
  norm_num [Label,Fintype.card_prod]
lemma chart_integral_domain(j:Label 3):IsDomain (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j
lemma chart_finite_type(j:Label 3):Algebra.FiniteType ℂ (CoordinateChart τ hτ j):=
  PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
end PELOriginalCandidateNineChartCover318
