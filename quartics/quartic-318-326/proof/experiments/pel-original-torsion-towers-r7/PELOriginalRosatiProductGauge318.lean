module
public import PELOriginalRosatiProductFrames318
public section
noncomputable section
namespace PELOriginalRosatiProductGauge318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318 PELOriginalRosatiProductMaps318
open PELPrincipalOrderCoordinates318
open PELOriginalRosatiProductCover318 PELOriginalHyperplaneAllPowerBasis318 PELOriginalRosatiProductFrames318
open PELOriginalRosatiSelectedUnits318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (N : ℕ) [NeZero N] (D : Data τ hτ N)
local instance productReduced : IsReduced (Product τ hτ) := product_reduced τ hτ
@[expose] def gauge (b : PELOriginalRosatiProductCover318.Index τ hτ) : Γ(Product τ hτ,chart τ hτ a b)ˣ :=
  unit τ hτ a N D true b*(unit τ hτ a N D false b)⁻¹
lemma gaugeProduct_nonzero (side : Bool) (b : PELOriginalRosatiProductCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    gaugeProduct τ hτ a N D side b z w≠0 := by
  have hn (t : Fin 9) := D.lineData.nonzero _ _ (point_mem τ hτ a b p z w hp t)
  exact mul_ne_zero (mul_ne_zero (hn _) (hn _)) (hn _)
lemma gauge_value (b : PELOriginalRosatiProductCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    ComplexOpenPointEvaluation318.evaluation _ p (gauge τ hτ a N D b).val=
      gaugeProduct τ hτ a N D true b z w/gaugeProduct τ hτ a N D false b z w := by
  let ev := ComplexOpenPointEvaluation318.evaluation (chart τ hτ a b) p
  have hi (u : Γ(Product τ hτ,chart τ hτ a b)ˣ) : ev (u⁻¹).val=(ev u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map ev.toMonoidHom) u)
  rw [gauge,Units.val_mul,map_mul,hi,unit_value,unit_value,
    regular_evaluation τ hτ a N D true b p z w hp,
    regular_evaluation τ hτ a N D false b p z w hp]
  have hn (t : Fin 9) : D.lineData.g (b t) (argument a z w t)≠0 :=
    D.lineData.nonzero _ _ (point_mem τ hτ a b p z w hp t)
  have h0 := hn 0;have h1 := hn 1;have h2 := hn 2;have h3 := hn 3;have h4 := hn 4
  have h5 := hn 5;have h6 := hn 6;have h7 := hn 7;have h8 := hn 8
  dsimp only [argument,Matrix.cons_val_zero,Matrix.cons_val_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [numerator,gaugeProduct,positions,mainPositions,argument,Fin.prod_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7,h8]
  <;> ring

/-- Full regular cocycle equality on the WHOLE product scheme. Auxiliary
ninefold factors cancel as genuine regular units, not just meromorphically. -/
lemma gauge_equation (b c : PELOriginalRosatiProductCover318.Index τ hτ) :
    (LineFrameCocycle318.cocycle (sheaf τ hτ a N D false) (chart τ hτ a)
      (frame τ hτ a N D false)).transition b c=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (Product τ hτ)).obj
      (chart τ hτ a) (gauge τ hτ a N D) b c*
      (LineFrameCocycle318.cocycle (sheaf τ hτ a N D true) (chart τ hτ a)
        (frame τ hτ a N D true)).transition b c := by
  let W := chart τ hτ a b ⊓ chart τ hτ a c
  apply Units.ext
  apply ComplexOpenPointEvaluation318.ext (baseMap τ hτ) W
  intro p hp
  obtain ⟨z,w,he⟩ := point_representation τ hτ W p hp
  let pL := p≫(Product τ hτ).homOfLE (show W≤chart τ hτ a b from inf_le_left)
  let pR := p≫(Product τ hτ).homOfLE (show W≤chart τ hτ a c from inf_le_right)
  have hL : pL≫(chart τ hτ a b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w) := by
    simpa only [pL,Category.assoc,Scheme.homOfLE_ι] using he
  have hR : pR≫(chart τ hτ a c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w) := by
    simpa only [pR,Category.assoc,Scheme.homOfLE_ι] using he
  rw [transition_value τ hτ a N D false b c p z w he]
  have hi (u : Γ(Product τ hτ,W)ˣ) : ComplexOpenPointEvaluation318.evaluation W p (u⁻¹).val=
      (ComplexOpenPointEvaluation318.evaluation W p u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map (ComplexOpenPointEvaluation318.evaluation W p).toMonoidHom) u)
  simp only [UnitTransitionCocycle318.coboundary,Units.val_mul,Units.coe_map]
  rw [map_mul,map_mul,hi,ComplexOpenPointEvaluation318.restriction,
    ComplexOpenPointEvaluation318.restriction,gauge_value τ hτ a N D b pL z w hL,
    gauge_value τ hτ a N D c pR z w hR,transition_value τ hτ a N D true b c p z w he]
  field_simp [gaugeProduct_nonzero τ hτ a N D true b pL z w hL,
    gaugeProduct_nonzero τ hτ a N D false b pL z w hL,
    gaugeProduct_nonzero τ hτ a N D true c pR z w hR,
    gaugeProduct_nonzero τ hτ a N D false c pR z w hR]

/-- Actual unsquared Rosati-product comparison from a whole regular unit gauge. This is an isomorphism on the ENTIRE original product. -/
@[expose] def iso : sheaf τ hτ a N D true ≅ sheaf τ hτ a N D false :=
  FramedLineUnitGaugeIso318.iso _ _ (chart τ hτ a) (frame τ hτ a N D true)
    (frame τ hτ a N D false) (covers τ hτ a) (gauge τ hτ a N D) (gauge_equation τ hτ a N D)
end PELOriginalRosatiProductGauge318
