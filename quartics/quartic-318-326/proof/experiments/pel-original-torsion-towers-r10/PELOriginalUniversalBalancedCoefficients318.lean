module
public import PELOriginalBalancedDoubleExpansion318
public import ComplexBilinearOpenCoefficients318
public import PELOriginalBalancedHyperplaneSquares318
public import PELOriginalProductComplexPoints318
public section
noncomputable section
namespace PELOriginalUniversalBalancedCoefficients318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalCandidateComplexPoints318 PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalBalancedLineData318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (2*N)]

/-- Actual regular doubled-degree basis coefficients, together with
independently defined original line frames. No product-family isomorphism
or universal theorem of square occurs among these inputs. -/
structure Data where
  lineData : PELOriginalBalancedLineData318.Data τ hτ
  label : NonemptyIndex τ hτ → Label N
  gauge : ∀ i z,lineData.g i z=PELOriginalLevelPowerSections318.value τ hτ N (label i) z
  basis : ∀ (i : NonemptyIndex τ hτ) (r : Label (2*N)),Γ(candidate τ hτ,opens τ hτ i)
  basis_value : ∀ i r z,z∈domain τ hτ (opens τ hτ i) →
    value τ hτ (opens τ hτ i) (basis i r) z=
      PELOriginalLevelPowerSections318.value τ hτ (2*N) r z/(lineData.g i z)^2

abbrev first : Product τ hτ ⟶ candidate τ hτ := pullback.fst _ _
abbrev second : Product τ hτ ⟶ candidate τ hτ := pullback.snd _ _
abbrev sourceOpen (i j : NonemptyIndex τ hτ) :=
  ComplexBilinearOpenCoefficients318.domain (first τ hτ) (second τ hτ) (opens τ hτ i) (opens τ hτ j)
variable (D : Data τ hτ N)

/-- Genuine regular balanced products on the WHOLE product mixed chart,
using fixed finite double coefficients and actual scalar/pullback maps. -/
@[expose] def regular (k l : NonemptyIndex τ hτ) (i j : Label N) :
    Γ(Product τ hτ,sourceOpen τ hτ k l) :=
  ComplexBilinearOpenCoefficients318.sum (baseMap τ hτ) (first τ hτ) (second τ hτ)
    (opens τ hτ k) (opens τ hτ l)
    (PELOriginalBalancedDoubleExpansion318.coefficients τ hτ N i j) (D.basis k) (D.basis l)

lemma regular_evaluation (k l : NonemptyIndex τ hτ) (i j : Label N)
    (p : Spec (CommRingCat.of ℂ) ⟶ (sourceOpen τ hτ k l).toScheme)
    (z a : ComplexVectors) (hz : z∈domain τ hτ (opens τ hτ k))
    (ha : a∈domain τ hτ (opens τ hτ l))
    (hp : p≫(sourceOpen τ hτ k l).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a)) :
    ComplexOpenPointEvaluation318.evaluation (sourceOpen τ hτ k l) p (regular τ hτ N D k l i j)=
      (PELOriginalLevelPowerSections318.value τ hτ N i (z+a)*
        PELOriginalLevelPowerSections318.value τ hτ N j (z-a))/
        ((D.lineData.g k z)^2*(D.lineData.g l a)^2) := by
  let q := point τ hτ (opens τ hτ k) z hz
  let t := point τ hτ (opens τ hτ l) a ha
  have hq : p≫(sourceOpen τ hτ k l).ι≫first τ hτ=q≫(opens τ hτ k).ι := by
    rw [←Category.assoc,hp,point_ι,pair_fst]
  have ht : p≫(sourceOpen τ hτ k l).ι≫second τ hτ=t≫(opens τ hτ l).ι := by
    rw [←Category.assoc,hp,point_ι,pair_snd]
  have hpC : p≫(sourceOpen τ hτ k l).ι≫baseMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hp,pair_over]
  rw [regular,ComplexBilinearOpenCoefficients318.sum_evaluation
    (baseMap τ hτ) (first τ hτ) (second τ hτ) _ _ _ _ _ p hpC q t hq ht]
  have hqv (u : Label (2*N)) : ComplexOpenPointEvaluation318.evaluation (opens τ hτ k) q (D.basis k u)=
      PELOriginalLevelPowerSections318.value τ hτ (2*N) u z/(D.lineData.g k z)^2 := by
    exact (value_at_point τ hτ _ _ z q (point_ι τ hτ _ z hz)).symm.trans (D.basis_value k u z hz)
  have htv (u : Label (2*N)) : ComplexOpenPointEvaluation318.evaluation (opens τ hτ l) t (D.basis l u)=
      PELOriginalLevelPowerSections318.value τ hτ (2*N) u a/(D.lineData.g l a)^2 := by
    exact (value_at_point τ hτ _ _ a t (point_ι τ hτ _ a ha)).symm.trans (D.basis_value l u a ha)
  simp_rw [hqv,htv]
  rw [←PELOriginalBalancedDoubleExpansion318.paired,PELOriginalBalancedDoubleExpansion318.formula,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  field_simp [D.lineData.nonzero k z hz,D.lineData.nonzero l a ha]
  <;> ring
end PELOriginalUniversalBalancedCoefficients318
