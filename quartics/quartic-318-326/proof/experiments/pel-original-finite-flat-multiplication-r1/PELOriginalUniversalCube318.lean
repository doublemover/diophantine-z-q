module
public import PELOriginalCubeLineFrames318
public section
noncomputable section
namespace PELOriginalUniversalCube318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318 PELOriginalCubeSchemeMaps318
open PELOriginalCubeOpenCover318 PELOriginalCubeBasisCoefficients318 PELOriginalCubeLineFrames318
open PELOriginalCubeRegularCoefficients318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (4*N)] (D : Data τ hτ N)
local instance tripleReduced : IsReduced (Triple τ hτ) := triple_reduced τ hτ
@[expose] def gauge (b : PELOriginalCubeOpenCover318.Index τ hτ) : Γ(Triple τ hτ,chart τ hτ b)ˣ :=
  unit τ hτ N D true b*(unit τ hτ N D false b)⁻¹
lemma gaugeProduct_nonzero (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme) (x y z : ComplexVectors)
    (hp : p≫(chart τ hτ b).ι=triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) :
    gaugeProduct τ hτ N D side b x y z≠0 := by
  have hn (t : Fin 11) := D.lineData.nonzero _ _ (point_mem τ hτ b p x y z hp t)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn _) (hn _)) (hn _)) (hn _)
lemma gauge_value (b : PELOriginalCubeOpenCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme) (x y z : ComplexVectors)
    (hp : p≫(chart τ hτ b).ι=triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) :
    ComplexOpenPointEvaluation318.evaluation _ p (gauge τ hτ N D b).val=
      gaugeProduct τ hτ N D true b x y z/gaugeProduct τ hτ N D false b x y z := by
  let ev := ComplexOpenPointEvaluation318.evaluation (chart τ hτ b) p
  have hi (u : Γ(Triple τ hτ,chart τ hτ b)ˣ) : ev (u⁻¹).val=(ev u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map ev.toMonoidHom) u)
  rw [gauge,Units.val_mul,map_mul,hi,unit_value,unit_value,
    regular_evaluation τ hτ N D true b p x y z hp,
    regular_evaluation τ hτ N D false b p x y z hp,selected_value,selected_value]
  have hn (t : Fin 11) : D.lineData.g (b t) (argument x y z t)≠0 :=
    D.lineData.nonzero _ _ (point_mem τ hτ b p x y z hp t)
  have h0 := hn 0;have h1 := hn 1;have h2 := hn 2;have h3 := hn 3;have h4 := hn 4
  have h5 := hn 5;have h6 := hn 6;have h7 := hn 7;have h8 := hn 8;have h9 := hn 9;have h10 := hn 10
  dsimp only [argument,Matrix.cons_val_zero,Matrix.cons_val_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [numerator,gaugeProduct,positions,argument,Bool.false_eq_true,if_true,if_false,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  <;> ring

/-- Full regular cocycle equality on the WHOLE triple scheme. Auxiliary
sevenfold factors cancel as genuine regular units, not just meromorphically. -/
lemma gauge_equation (b c : PELOriginalCubeOpenCover318.Index τ hτ) :
    (LineFrameCocycle318.cocycle (sheaf τ hτ N D false) (chart τ hτ)
      (frame τ hτ N D false)).transition b c=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (Triple τ hτ)).obj
      (chart τ hτ) (gauge τ hτ N D) b c*
      (LineFrameCocycle318.cocycle (sheaf τ hτ N D true) (chart τ hτ)
        (frame τ hτ N D true)).transition b c := by
  let W := chart τ hτ b ⊓ chart τ hτ c
  apply Units.ext
  apply ComplexOpenPointEvaluation318.ext (structureMap τ hτ) W
  intro p hp
  obtain ⟨x,y,z,he⟩ := point_representation τ hτ W p hp
  let pL := p≫(Triple τ hτ).homOfLE (show W≤chart τ hτ b from inf_le_left)
  let pR := p≫(Triple τ hτ).homOfLE (show W≤chart τ hτ c from inf_le_right)
  have hL : pL≫(chart τ hτ b).ι=triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z) := by
    simpa only [pL,Category.assoc,Scheme.homOfLE_ι] using he
  have hR : pR≫(chart τ hτ c).ι=triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z) := by
    simpa only [pR,Category.assoc,Scheme.homOfLE_ι] using he
  rw [transition_value τ hτ N D false b c p x y z he]
  have hi (u : Γ(Triple τ hτ,W)ˣ) : ComplexOpenPointEvaluation318.evaluation W p (u⁻¹).val=
      (ComplexOpenPointEvaluation318.evaluation W p u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using congrArg Units.val
      (map_inv (Units.map (ComplexOpenPointEvaluation318.evaluation W p).toMonoidHom) u)
  simp only [UnitTransitionCocycle318.coboundary,Units.val_mul,Units.coe_map]
  rw [map_mul,map_mul,hi,ComplexOpenPointEvaluation318.restriction,
    ComplexOpenPointEvaluation318.restriction,gauge_value τ hτ N D b pL x y z hL,
    gauge_value τ hτ N D c pR x y z hR,transition_value τ hτ N D true b c p x y z he]
  field_simp [gaugeProduct_nonzero τ hτ N D true b pL x y z hL,
    gaugeProduct_nonzero τ hτ N D false b pL x y z hL,
    gaugeProduct_nonzero τ hτ N D true c pR x y z hR,
    gaugeProduct_nonzero τ hτ N D false c pR x y z hR]

/-- Actual universal cube isomorphism, with the genuine zero-map factor
included. This is an isomorphism on the ENTIRE original triple product. -/
@[expose] def iso : sheaf τ hτ N D true ≅ sheaf τ hτ N D false :=
  FramedLineUnitGaugeIso318.iso _ _ (chart τ hτ) (frame τ hτ N D true)
    (frame τ hτ N D false) (covers τ hτ) (gauge τ hτ N D) (gauge_equation τ hτ N D)
end PELOriginalUniversalCube318
