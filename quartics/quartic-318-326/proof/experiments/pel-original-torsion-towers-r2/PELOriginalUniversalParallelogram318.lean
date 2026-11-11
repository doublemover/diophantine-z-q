module
public import PELOriginalParallelogramRegularGauge318
public section
noncomputable section
namespace PELOriginalUniversalParallelogram318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalUniversalBalancedCoefficients318 PELOriginalParallelogramCover318
open PELOriginalParallelogramFrames318 PELOriginalParallelogramRegularGauge318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (2*N)]
variable (D : PELOriginalUniversalBalancedCoefficients318.Data τ hτ N)
local instance productReduced : IsReduced (Product τ hτ) := product_reduced τ hτ

/-- The universal parallelogram gauge equation on the WHOLE product,
proved from regular functions before reconstructing any sheaf map. -/
lemma gauge_equation (b c : Index τ hτ) :
    (LineFrameCocycle318.cocycle (sourceSheaf τ hτ N D) (chart τ hτ)
      (sourceFrame τ hτ N D)).transition b c=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (Product τ hτ)).obj
      (chart τ hτ) (unit τ hτ N D) b c *
      (LineFrameCocycle318.cocycle (targetSheaf τ hτ N D) (chart τ hτ)
        (targetFrame τ hτ N D)).transition b c := by
  let W := chart τ hτ b ⊓ chart τ hτ c
  apply Units.ext
  apply ComplexOpenPointEvaluation318.ext (baseMap τ hτ) W
  intro p hp
  obtain ⟨z,a,he⟩ := point_representation τ hτ W p hp
  let pL := p≫(Product τ hτ).homOfLE (show W≤chart τ hτ b from inf_le_left)
  let pR := p≫(Product τ hτ).homOfLE (show W≤chart τ hτ c from inf_le_right)
  have hL : pL≫(chart τ hτ b).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a) := by
    simpa only [pL,Category.assoc,Scheme.homOfLE_ι] using he
  have hR : pR≫(chart τ hτ c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a) := by
    simpa only [pR,Category.assoc,Scheme.homOfLE_ι] using he
  rw [source_transition_value τ hτ N D b c p z a he]
  have hinv (u : Γ(Product τ hτ,W)ˣ) :
      ComplexOpenPointEvaluation318.evaluation W p (u⁻¹).val=
        (ComplexOpenPointEvaluation318.evaluation W p u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map (ComplexOpenPointEvaluation318.evaluation W p).toMonoidHom) u)
  simp only [UnitTransitionCocycle318.coboundary,Units.val_mul,Units.coe_map]
  rw [map_mul,map_mul,hinv,ComplexOpenPointEvaluation318.restriction,
    ComplexOpenPointEvaluation318.restriction,unit_value,unit_value,
    regular_value τ hτ N D b pL z a hL,regular_value τ hτ N D c pR z a hR,
    target_transition_value τ hτ N D b c p z a he]
  have hb (t : Fin 4) : D.lineData.g (b t) (argument z a t)≠0 :=
    D.lineData.nonzero _ _ (point_mem τ hτ b pL z a hL t)
  have hc (t : Fin 4) : D.lineData.g (c t) (argument z a t)≠0 :=
    D.lineData.nonzero _ _ (point_mem τ hτ c pR z a hR t)
  have hb0 := hb 0; have hb1 := hb 1; have hb2 := hb 2; have hb3 := hb 3
  have hc0 := hc 0; have hc1 := hc 1; have hc2 := hc 2; have hc3 := hc 3
  change D.lineData.g (b 0) z≠0 at hb0
  change D.lineData.g (b 1) a≠0 at hb1
  change D.lineData.g (b 2) (z+a)≠0 at hb2
  change D.lineData.g (b 3) (z-a)≠0 at hb3
  change D.lineData.g (c 0) z≠0 at hc0
  change D.lineData.g (c 1) a≠0 at hc1
  change D.lineData.g (c 2) (z+a)≠0 at hc2
  change D.lineData.g (c 3) (z-a)≠0 at hc3
  field_simp [hb0,hb1,hb2,hb3,hc0,hc1,hc2,hc3]

/-- Actual inverse module-sheaf maps on the full scheme product, not a
collection of parameter-wise isomorphisms. -/
@[expose] def iso : targetSheaf τ hτ N D ≅ sourceSheaf τ hτ N D :=
  FramedLineUnitGaugeIso318.iso _ _ (chart τ hτ) (targetFrame τ hτ N D)
    (sourceFrame τ hτ N D) (covers τ hτ) (unit τ hτ N D) (gauge_equation τ hτ N D)
lemma hom_inv : (iso τ hτ N D).hom≫(iso τ hτ N D).inv=𝟙 _ := (iso τ hτ N D).hom_inv_id
lemma inv_hom : (iso τ hτ N D).inv≫(iso τ hτ N D).hom=𝟙 _ := (iso τ hτ N D).inv_hom_id
end PELOriginalUniversalParallelogram318
