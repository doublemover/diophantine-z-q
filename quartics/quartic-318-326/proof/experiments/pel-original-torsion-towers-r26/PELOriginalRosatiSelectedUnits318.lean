module
public import PELOriginalRosatiProductCover318
public section
noncomputable section
namespace PELOriginalRosatiSelectedUnits318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELPrincipalOrderCoordinates318 PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318 PELOriginalRosatiProductMaps318
open PELOriginalRosatiProductCover318 PELOriginalHyperplaneAllPowerBasis318
open PELOriginalRosatiPositiveForms318 PELOriginalRosatiDoubleExpansion318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (N : ℕ) [NeZero N] (D : Data τ hτ N)
@[expose] def selected (side : Bool) (b : Index τ hτ) : Fin 9 → Label N :=
  fun i => D.label (b (positions side i))
@[expose] def regular (side : Bool) (b : Index τ hτ) : Γ(Product τ hτ,chart τ hτ a b) :=
  (Product τ hτ).presheaf.map (homOfLE (source_le τ hτ a b)).op
    (PELOriginalRosatiRegularCoefficients318.regular τ hτ a N D (b 0) (b 1)
      side (selected τ hτ N D side b))
@[expose] def numerator (side : Bool) (b : Index τ hτ) (z w : ComplexVectors) : ℂ :=
  ∏ i : Fin 9,D.lineData.g (b (positions side i))
    (PELOriginalRosatiProductMaps318.argument a z w (positions side i))
lemma selected_value (side : Bool) (b : Index τ hτ) (z w : ComplexVectors) :
    PELOriginalRosatiDoubleExpansion318.value τ hτ a N side (selected τ hτ N D side b) z w=
      numerator τ hτ a N D side b z w := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [PELOriginalRosatiProductMaps318.argument_positions,←D.gauge]
lemma regular_evaluation (side : Bool) (b : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    ComplexOpenPointEvaluation318.evaluation _ p (regular τ hτ a N D side b)=
      numerator τ hτ a N D side b z w/
        (D.lineData.g (b 0) z^(firstWeight a)*D.lineData.g (b 1) w^(secondWeight a)) := by
  rw [regular,ComplexOpenPointEvaluation318.restriction]
  have he : (p≫(Product τ hτ).homOfLE (source_le τ hτ a b))≫
      (PELOriginalRosatiRegularCoefficients318.sourceOpen τ hτ (b 0) (b 1)).ι=
        pair τ hτ (projection (P τ) z) (projection (P τ) w) := by
    rw [Category.assoc,Scheme.homOfLE_ι]; exact hp
  rw [PELOriginalRosatiRegularCoefficients318.regular_evaluation τ hτ a N D (b 0) (b 1)
    side _ _ z w (point_mem τ hτ a b p z w hp 0) (point_mem τ hτ a b p z w hp 1) he,selected_value]
lemma numerator_nonzero (side : Bool) (b : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    numerator τ hτ a N D side b z w≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact D.lineData.nonzero _ _ (point_mem τ hτ a b p z w hp (positions side i))
lemma regular_unit (side : Bool) (b : Index τ hτ) : IsUnit (regular τ hτ a N D side b) := by
  apply ComplexOpenPointEvaluation318.isUnit (baseMap τ hτ) (chart τ hτ a b)
  intro p hp
  obtain ⟨z,w,he⟩ := point_representation τ hτ _ p hp
  rw [regular_evaluation τ hτ a N D side b p z w he]
  exact div_ne_zero (numerator_nonzero τ hτ a N D side b p z w he)
    (mul_ne_zero (pow_ne_zero _ (D.lineData.nonzero _ _ (point_mem τ hτ a b p z w he 0)))
      (pow_ne_zero _ (D.lineData.nonzero _ _ (point_mem τ hτ a b p z w he 1))))
@[expose] def unit (side : Bool) (b : Index τ hτ) := (regular_unit τ hτ a N D side b).unit
lemma unit_value (side : Bool) (b : Index τ hτ) :
    (unit τ hτ a N D side b).val=regular τ hτ a N D side b := IsUnit.unit_spec _
end PELOriginalRosatiSelectedUnits318
