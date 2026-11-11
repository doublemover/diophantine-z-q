module
public import PELOriginalParallelogramFrames318
public section
noncomputable section
namespace PELOriginalParallelogramRegularGauge318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalUniversalBalancedCoefficients318 PELOriginalParallelogramCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (2*N)]
variable (D : PELOriginalUniversalBalancedCoefficients318.Data τ hτ N)
@[expose] def regular (b : Index τ hτ) : Γ(Product τ hτ,chart τ hτ b) :=
  (Product τ hτ).presheaf.map (homOfLE (source_le τ hτ b)).op
    (PELOriginalUniversalBalancedCoefficients318.regular τ hτ N D (b 0) (b 1)
      (D.label (b 2)) (D.label (b 3)))

lemma regular_value (b : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme)
    (z a : ComplexVectors)
    (hp : p≫(chart τ hτ b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a)) :
    ComplexOpenPointEvaluation318.evaluation _ p (regular τ hτ N D b)=
      (D.lineData.g (b 2) (z+a)*D.lineData.g (b 3) (z-a))/
        ((D.lineData.g (b 0) z)^2*(D.lineData.g (b 1) a)^2) := by
  rw [regular,ComplexOpenPointEvaluation318.restriction]
  have hq : (p≫(Product τ hτ).homOfLE (source_le τ hτ b))≫(sourceOpen τ hτ (b 0) (b 1)).ι=
      pair τ hτ (projection (P τ) z) (projection (P τ) a) := by
    rw [Category.assoc,Scheme.homOfLE_ι]; exact hp
  rw [PELOriginalUniversalBalancedCoefficients318.regular_evaluation τ hτ N D (b 0) (b 1)
    _ _ _ z a (point_mem τ hτ b p z a hp 0) (point_mem τ hτ b p z a hp 1) hq,
    ←D.gauge (b 2) (z+a),←D.gauge (b 3) (z-a)]

lemma isUnit (b : Index τ hτ) : IsUnit (regular τ hτ N D b) := by
  apply ComplexOpenPointEvaluation318.isUnit (baseMap τ hτ)
  intro p hp
  obtain ⟨z,a,he⟩ := point_representation τ hτ _ p hp
  rw [regular_value τ hτ N D b p z a he]
  exact div_ne_zero
    (mul_ne_zero (D.lineData.nonzero _ _ (point_mem τ hτ b p z a he 2))
      (D.lineData.nonzero _ _ (point_mem τ hτ b p z a he 3)))
    (mul_ne_zero (pow_ne_zero _ (D.lineData.nonzero _ _ (point_mem τ hτ b p z a he 0)))
      (pow_ne_zero _ (D.lineData.nonzero _ _ (point_mem τ hτ b p z a he 1))))
@[expose] def unit (b : Index τ hτ) : Γ(Product τ hτ,chart τ hτ b)ˣ := (isUnit τ hτ N D b).unit
lemma unit_value (b : Index τ hτ) : (unit τ hτ N D b).val=regular τ hτ N D b :=
  (isUnit τ hτ N D b).unit_spec
end PELOriginalParallelogramRegularGauge318
