module
public import PELOriginalCubeSchemeMaps318
public import ComplexTrilinearOpenCoefficients318
public section
noncomputable section
namespace PELOriginalCubeOpenCover318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318 PELOriginalMixedRatioCover318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318 PELOriginalCubeSchemeMaps318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Index := Fin 11 → NonemptyIndex τ hτ
@[expose] def chart (b : Index τ hτ) : (Triple τ hτ).Opens := ⨅ t : Fin 11,maps τ hτ t ⁻¹ᵁ opens τ hτ (b t)
lemma chart_le (b : Index τ hτ) (t : Fin 11) : chart τ hτ b≤maps τ hτ t ⁻¹ᵁ opens τ hτ (b t) := iInf_le _ t
lemma covers : (⊤ : (Triple τ hτ).Opens)≤⨆ b,chart τ hτ b := by
  intro x hx
  have hm (t : Fin 11) : ∃ i : NonemptyIndex τ hτ,maps τ hτ t x∈opens τ hτ i :=
    TopologicalSpace.Opens.mem_iSup.mp (coversTop τ hτ (show maps τ hτ t x∈⊤ from trivial))
  choose b hb using hm
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨b,TopologicalSpace.Opens.mem_iInf.mpr hb⟩
@[expose] def sourceMaps : Fin 3 → Triple τ hτ ⟶ candidate τ hτ := fun t => maps τ hτ ⟨t.val,by omega⟩
@[expose] def sourceOpens (b : Index τ hτ) : Fin 3 → (candidate τ hτ).Opens :=
  fun t => opens τ hτ (b ⟨t.val,by omega⟩)
abbrev sourceDomain (b : Index τ hτ) := ComplexTrilinearOpenCoefficients318.domain (sourceMaps τ hτ) (sourceOpens τ hτ b)
lemma source_le (b : Index τ hτ) : chart τ hτ b≤sourceDomain τ hτ b :=
  le_iInf (fun t => chart_le τ hτ b ⟨t.val,by omega⟩)
lemma point_representation (U : (Triple τ hτ).Opens) (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫U.ι≫structureMap τ hτ=𝟙 _) :
    ∃ x y z : ComplexVectors,p≫U.ι=triple τ hτ (projection (P τ) x)
      (projection (P τ) y) (projection (P τ) z) := every_point τ hτ (p≫U.ι) hp
lemma point_mem (b : Index τ hτ) (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme)
    (x y z : ComplexVectors) (hp : p≫(chart τ hτ b).ι=triple τ hτ
      (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) (t : Fin 11) :
    argument x y z t∈PELOriginalOpenRegularFunction318.domain τ hτ (opens τ hτ (b t)) := by
  change candidateComplexPoint τ hτ (projection (P τ) (argument x y z t)) (IsLocalRing.closedPoint ℂ)∈_
  rw [←point_action,←hp]
  exact chart_le τ hτ b t (p (IsLocalRing.closedPoint ℂ)).property
end PELOriginalCubeOpenCover318
