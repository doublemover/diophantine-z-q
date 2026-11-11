module
public import PELOriginalRosatiProductMaps318
public import PELOriginalProductLineScalarEvaluation318
public import PELOriginalUniversalHyperplaneInputs318
public import PELOriginalSchemeAdditionOperations318
public import PELOriginalPolarizationSymmetricSquare318
public section
noncomputable section
namespace PELOriginalRosatiProductCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalRosatiRegularCoefficients318 PELOriginalRosatiProductMaps318 PELPrincipalOrderCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
abbrev Index := Fin 9 → NonemptyIndex τ hτ
@[expose] def chart (b : Index τ hτ) : (Product τ hτ).Opens :=
  ⨅ t : Fin 9,maps τ hτ a t ⁻¹ᵁ opens τ hτ (b t)
lemma chart_le (b : Index τ hτ) (t : Fin 9) :
    chart τ hτ a b ≤ maps τ hτ a t ⁻¹ᵁ opens τ hτ (b t) := iInf_le _ t
lemma covers : (⊤ : (Product τ hτ).Opens) ≤ ⨆ b,chart τ hτ a b := by
  intro x hx
  have hm (t : Fin 9) : ∃ i : NonemptyIndex τ hτ,maps τ hτ a t x∈opens τ hτ i :=
    TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show maps τ hτ a t x∈⊤ from trivial))
  choose b hb using hm
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨b,?_⟩
  exact TopologicalSpace.Opens.mem_iInf.mpr hb
lemma source_le (b : Index τ hτ) : chart τ hτ a b ≤ sourceOpen τ hτ (b 0) (b 1) :=
  le_inf (chart_le τ hτ a b 0) (chart_le τ hτ a b 1)

/-- Every actual open point retains its original ordered pair and all
NINE memberships. No dense-locus replacement of the product is used. -/
lemma point_representation (U : (Product τ hτ).Opens)
    (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫U.ι≫baseMap τ hτ=𝟙 _) :
    ∃ z w : ComplexVectors,p≫U.ι=pair τ hτ (projection (P τ) z) (projection (P τ) w) :=
  every_point τ hτ (p≫U.ι) hp
lemma point_mem (b : Index τ hτ) (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b).toScheme)
    (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w))
    (t : Fin 9) : argument a z w t∈PELOriginalOpenRegularFunction318.domain τ hτ (opens τ hτ (b t)) := by
  change candidateComplexPoint τ hτ (projection (P τ) (argument a z w t)) (IsLocalRing.closedPoint ℂ)∈_
  rw [←point_action,←hp]
  exact chart_le τ hτ a b t (p (IsLocalRing.closedPoint ℂ)).property
end PELOriginalRosatiProductCover318
