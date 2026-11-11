module
public import PELOriginalRosatiDoubleExpansion318
public import PELOriginalHyperplaneAllPowerBasis318
public import ComplexBilinearOpenCoefficients318
public import PELOriginalBalancedHyperplaneSquares318
public import PELOriginalProductComplexPoints318
public section
noncomputable section
namespace PELOriginalRosatiRegularCoefficients318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalCandidateComplexPoints318 PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalBalancedLineData318 PELOriginalLevelTheta318
open PELPrincipalOrderCoordinates318 PELOriginalRosatiPositiveForms318
open PELOriginalRosatiDoubleExpansion318 PELOriginalHyperplaneAllPowerBasis318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (N : ℕ) [NeZero N]
local instance leftNonzero : NeZero (leftDegree a N) := ⟨by dsimp [leftDegree,firstWeight]; positivity⟩
local instance rightNonzero : NeZero (rightDegree a N) := ⟨by dsimp [rightDegree,secondWeight]; positivity⟩

abbrev first : Product τ hτ ⟶ candidate τ hτ := pullback.fst _ _
abbrev second : Product τ hτ ⟶ candidate τ hτ := pullback.snd _ _
abbrev sourceOpen (i j : NonemptyIndex τ hτ) :=
  ComplexBilinearOpenCoefficients318.domain (first τ hτ) (second τ hτ) (opens τ hτ i) (opens τ hτ j)
variable (D : Data τ hτ N)

/-- Genuine regular balanced products on the WHOLE product mixed chart,
using fixed finite double coefficients and actual scalar/pullback maps. -/
@[expose] def regular (k l : NonemptyIndex τ hτ) (side : Bool) (i : Fin 9 → Label N) :
    Γ(Product τ hτ,sourceOpen τ hτ k l) :=
  ComplexBilinearOpenCoefficients318.sum (baseMap τ hτ) (first τ hτ) (second τ hτ)
    (opens τ hτ k) (opens τ hτ l)
    (PELOriginalRosatiDoubleExpansion318.coefficients τ hτ a N side i) (D.basis (firstWeight a) k) (D.basis (secondWeight a) l)

lemma regular_evaluation (k l : NonemptyIndex τ hτ) (side : Bool) (i : Fin 9 → Label N)
    (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen τ hτ k l).toScheme)
    (z w : ComplexVectors) (hz : z∈domain τ hτ (opens τ hτ k))
    (ha : w∈domain τ hτ (opens τ hτ l))
    (hp : p≫(sourceOpen τ hτ k l).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    ComplexOpenPointEvaluation318.evaluation (sourceOpen τ hτ k l) p (regular τ hτ a N D k l side i)=
      PELOriginalRosatiDoubleExpansion318.value τ hτ a N side i z w/
        ((D.lineData.g k z)^(firstWeight a)*(D.lineData.g l w)^(secondWeight a)) := by
  let q := point τ hτ (opens τ hτ k) z hz
  let t := point τ hτ (opens τ hτ l) w ha
  have hq : p≫(sourceOpen τ hτ k l).ι≫first τ hτ=q≫(opens τ hτ k).ι := by
    rw [←Category.assoc,hp,point_ι,pair_fst]
  have ht : p≫(sourceOpen τ hτ k l).ι≫second τ hτ=t≫(opens τ hτ l).ι := by
    rw [←Category.assoc,hp,point_ι,pair_snd]
  have hpC : p≫(sourceOpen τ hτ k l).ι≫baseMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hp,pair_over]
  rw [regular,ComplexBilinearOpenCoefficients318.sum_evaluation
    (baseMap τ hτ) (first τ hτ) (second τ hτ) _ _ _ _ _ p hpC q t hq ht]
  have hqv (u : Label (leftDegree a N)) : ComplexOpenPointEvaluation318.evaluation (opens τ hτ k) q (D.basis (firstWeight a) k u)=
      PELOriginalLevelPowerSections318.value τ hτ (leftDegree a N) u z/(D.lineData.g k z)^(firstWeight a) := by
    exact (value_at_point τ hτ _ _ z q (point_ι τ hτ _ z hz)).symm.trans (D.basis_value (firstWeight a) k u z hz)
  have htv (u : Label (rightDegree a N)) : ComplexOpenPointEvaluation318.evaluation (opens τ hτ l) t (D.basis (secondWeight a) l u)=
      PELOriginalLevelPowerSections318.value τ hτ (rightDegree a N) u w/(D.lineData.g l w)^(secondWeight a) := by
    exact (value_at_point τ hτ _ _ w t (point_ι τ hτ _ w ha)).symm.trans (D.basis_value (secondWeight a) l u w ha)
  simp_rw [hqv,htv]
  rw [PELOriginalRosatiDoubleExpansion318.formula,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  field_simp [D.lineData.nonzero k z hz,D.lineData.nonzero l w ha]
  <;> ring
end PELOriginalRosatiRegularCoefficients318
