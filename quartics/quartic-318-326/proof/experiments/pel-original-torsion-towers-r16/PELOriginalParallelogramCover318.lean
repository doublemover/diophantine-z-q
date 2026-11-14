module
public import PELOriginalProductLineScalarEvaluation318
public import PELOriginalUniversalHyperplaneInputs318
public import PELOriginalSchemeAdditionOperations318
public import PELOriginalPolarizationSymmetricSquare318
public section
noncomputable section
namespace PELOriginalParallelogramCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalUniversalBalancedCoefficients318 PELOriginalSchemeAdditionOperations318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def difference : Product τ hτ ⟶ candidate τ hτ :=
  combine τ hτ (first τ hτ) (second τ hτ≫inverse τ hτ)
    (by rw [Category.assoc,inverse_over]; exact pullback.condition)
lemma difference_action (z a : ComplexVectors) :
    pair τ hτ (projection (P τ) z) (projection (P τ) a)≫difference τ hτ=
      candidateComplexPoint τ hτ (projection (P τ) (z-a)) := by
  have hg : pair τ hτ (projection (P τ) z) (projection (P τ) a)≫
      (second τ hτ≫inverse τ hτ)=candidateComplexPoint τ hτ (-projection (P τ) a) := by
    rw [←Category.assoc,pair_snd,inverse_action]
  have h := combine_action τ hτ (first τ hτ) (second τ hτ≫inverse τ hτ)
    (by rw [Category.assoc,inverse_over]; exact pullback.condition)
    (pair τ hτ (projection (P τ) z) (projection (P τ) a))
    (projection (P τ) z) (-projection (P τ) a) (pair_fst τ hτ _ _) hg
  apply h.trans
  apply congrArg (candidateComplexPoint τ hτ)
  symm
  rw [sub_eq_add_neg,PELOriginalAdditionSchemeMorphism318.projection_add,
    PELOriginalPolarizationSymmetricSquare318.projection_neg]


@[expose] def maps : Fin 4 → Product τ hτ ⟶ candidate τ hτ :=
  ![first τ hτ,second τ hτ,PELOriginalAdditionSchemeMorphism318.addition τ hτ,difference τ hτ]
@[expose] def argument (z a : ComplexVectors) : Fin 4 → ComplexVectors := ![z,a,z+a,z-a]
lemma point_action (t : Fin 4) (z a : ComplexVectors) :
    pair τ hτ (projection (P τ) z) (projection (P τ) a)≫maps τ hτ t=
      candidateComplexPoint τ hτ (projection (P τ) (argument z a t)) := by
  fin_cases t
  · exact pair_fst τ hτ _ _
  · exact pair_snd τ hτ _ _
  · exact PELOriginalAdditionSchemeMorphism318.original_point_action τ hτ z a
  · exact difference_action τ hτ z a
abbrev Index := Fin 4 → NonemptyIndex τ hτ
@[expose] def chart (b : Index τ hτ) : (Product τ hτ).Opens :=
  ⨅ t : Fin 4,maps τ hτ t ⁻¹ᵁ opens τ hτ (b t)
lemma chart_le (b : Index τ hτ) (t : Fin 4) :
    chart τ hτ b ≤ maps τ hτ t ⁻¹ᵁ opens τ hτ (b t) := iInf_le _ t
lemma covers : (⊤ : (Product τ hτ).Opens) ≤ ⨆ b,chart τ hτ b := by
  intro x hx
  have hm (t : Fin 4) : ∃ i : NonemptyIndex τ hτ,maps τ hτ t x∈opens τ hτ i :=
    TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show maps τ hτ t x∈⊤ from trivial))
  choose b hb using hm
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨b,?_⟩
  exact TopologicalSpace.Opens.mem_iInf.mpr hb
lemma source_le (b : Index τ hτ) : chart τ hτ b ≤ sourceOpen τ hτ (b 0) (b 1) :=
  le_inf (chart_le τ hτ b 0) (chart_le τ hτ b 1)

/-- Every actual open point retains its original ordered pair and all
FOUR memberships. No dense-locus replacement of the product is used. -/
lemma point_representation (U : (Product τ hτ).Opens)
    (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫U.ι≫baseMap τ hτ=𝟙 _) :
    ∃ z a : ComplexVectors,p≫U.ι=pair τ hτ (projection (P τ) z) (projection (P τ) a) :=
  every_point τ hτ (p≫U.ι) hp
lemma point_mem (b : Index τ hτ) (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme)
    (z a : ComplexVectors)
    (hp : p≫(chart τ hτ b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a))
    (t : Fin 4) : argument z a t∈PELOriginalOpenRegularFunction318.domain τ hτ (opens τ hτ (b t)) := by
  change candidateComplexPoint τ hτ (projection (P τ) (argument z a t)) (IsLocalRing.closedPoint ℂ)∈_
  rw [←point_action,←hp]
  exact chart_le τ hτ b t (p (IsLocalRing.closedPoint ℂ)).property
end PELOriginalParallelogramCover318
