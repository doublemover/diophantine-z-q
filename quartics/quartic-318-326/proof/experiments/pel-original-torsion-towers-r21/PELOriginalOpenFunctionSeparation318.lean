module
public import PELOriginalOpenRegularNaturality318
public import ReducedSchemeGlobalFunctionSeparation318
public import PELOriginalFullCandidateSchemePoints318
public section
noncomputable section
namespace PELOriginalOpenFunctionSeparation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalOpenRegularFunction318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- Every point of any actual open has an original representative,
retaining equality of the full Spec(C) morphism. -/
lemma point_representation (U : (candidate τ hτ).Opens)
    (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _) :
    ∃ z : ComplexVectors,z∈domain τ hτ U ∧
      p≫U.ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
  obtain ⟨j,z,hj,he⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ (p≫U.ι) hp
  have hz := he.trans (PELOriginalChartSchemePointIdentity318.chart_point τ hτ j z hj)
  refine ⟨z,?_,hz⟩
  change candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ)∈U
  rw [←hz]
  exact (p (IsLocalRing.closedPoint ℂ)).property

/-- Equality of genuine regular functions on the WHOLE open, proved
from all original points by the actual reduced Jacobson-scheme criterion. -/
theorem ext (U : (candidate τ hτ).Opens) (r s : Γ(candidate τ hτ,U))
    (h : ∀ z,z∈domain τ hτ U → value τ hτ U r z=value τ hτ U s z) : r=s := by
  let π := U.ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  apply (LineFrameTopScalar318.ringTop U).inv.injective
  apply ReducedSchemeGlobalFunctionSeparation318.ext π
  intro p hp
  obtain ⟨z,hz,he⟩ := point_representation τ hτ U p hp
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  have hs := h z hz
  rw [value_at_point τ hτ U r z p he,value_at_point τ hτ U s z p he] at hs
  exact hs

theorem unit_ext (U : (candidate τ hτ).Opens) (r s : Γ(candidate τ hτ,U)ˣ)
    (h : ∀ z,z∈domain τ hτ U → value τ hτ U r.val z=value τ hτ U s.val z) : r=s :=
  Units.ext (ext τ hτ U r.val s.val h)
end PELOriginalOpenFunctionSeparation318
