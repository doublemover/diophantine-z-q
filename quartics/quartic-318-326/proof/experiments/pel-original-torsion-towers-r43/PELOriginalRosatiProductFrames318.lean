module
public import PELOriginalRosatiSelectedUnits318
public section
noncomputable section
namespace PELOriginalRosatiProductFrames318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318 PELOriginalMixedRatioCover318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318 PELOriginalRosatiProductMaps318
open PELPrincipalOrderCoordinates318
open PELOriginalRosatiProductCover318 PELOriginalHyperplaneAllPowerBasis318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (N : ℕ) [NeZero N] (D : Data τ hτ N)
abbrev pulled (t : Fin 9) := (Scheme.Modules.pullback (maps τ hτ a t)).obj D.lineData.M
@[expose] def pulledFrame (t : Fin 9) (b : PELOriginalRosatiProductCover318.Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a b).toScheme.ringCatSheaf ≅
      (pulled τ hτ a N D t).restrict (chart τ hτ a b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (maps τ hτ a t) D.lineData.M (opens τ hτ (b t))
      (D.lineData.frame (b t))) (chart τ hτ a b) (chart_le τ hτ a b t)
@[expose] def mainPositions (side : Bool) : Fin 3 → Fin 9 := if side then ![4,0,3] else ![5,2,1]
abbrev pairSheaf (side : Bool) := IntrinsicTensorSheaf318.tensor
  (pulled τ hτ a N D (mainPositions side 0)) (pulled τ hτ a N D (mainPositions side 1))
abbrev threeSheaf (side : Bool) := IntrinsicTensorSheaf318.tensor (pairSheaf τ hτ a N D side)
  (pulled τ hτ a N D (mainPositions side 2))
abbrev sheaf (side : Bool) := threeSheaf τ hτ a N D side
@[expose] def pairFrame (side : Bool) (b : PELOriginalRosatiProductCover318.Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ a b)
    (pulledFrame τ hτ a N D (mainPositions side 0) b) (pulledFrame τ hτ a N D (mainPositions side 1) b)
@[expose] def threeFrame (side : Bool) (b : PELOriginalRosatiProductCover318.Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ a b) (pairFrame τ hτ a N D side b)
    (pulledFrame τ hτ a N D (mainPositions side 2) b)
@[expose] def frame (side : Bool) := threeFrame τ hτ a N D side

lemma pulled_scalar (t : Fin 9) (b c : PELOriginalRosatiProductCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b ⊓ chart τ hτ a c).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b ⊓ chart τ hτ a c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (pulled τ hτ a N D t) (chart τ hτ a)
        (pulledFrame τ hτ a N D t)).transition b c).val=
      D.lineData.g (c t) (argument a z w t)/D.lineData.g (b t) (argument a z w t) := by
  let W := chart τ hτ a b ⊓ chart τ hτ a c
  have hm : W≤maps τ hτ a t ⁻¹ᵁ (opens τ hτ (b t) ⊓ opens τ hτ (c t)) :=
    fun x hx => ⟨chart_le τ hτ a b t hx.1,chart_le τ hτ a c t hx.2⟩
  have he : p≫W.ι≫maps τ hτ a t=candidateComplexPoint τ hτ (projection (P τ) (argument a z w t)) := by
    rw [←Category.assoc,hp,point_action]
  change ComplexOpenPointEvaluation318.evaluation W p (FrameScalarAlgebra318.scalar _ _).val=_
  simp only [pulledFrame,OpenLineFrameRefinement318.coordinates]
  exact PELOriginalProductLineScalarEvaluation318.scalar_value τ hτ D.lineData
    (maps τ hτ a t) (b t) (c t) W hm p (argument a z w t) he
@[expose] def gaugeProduct (side : Bool) (b : PELOriginalRosatiProductCover318.Index τ hτ) (z w : ComplexVectors) : ℂ :=
  (D.lineData.g (b (mainPositions side 0)) (argument a z w (mainPositions side 0))*
    D.lineData.g (b (mainPositions side 1)) (argument a z w (mainPositions side 1))*
    D.lineData.g (b (mainPositions side 2)) (argument a z w (mainPositions side 2)))
lemma transition_value (side : Bool) (b c : PELOriginalRosatiProductCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a b ⊓ chart τ hτ a c).toScheme) (z w : ComplexVectors)
    (hp : p≫(chart τ hτ a b ⊓ chart τ hτ a c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) w)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (sheaf τ hτ a N D side) (chart τ hτ a)
        (frame τ hτ a N D side)).transition b c).val=
      gaugeProduct τ hτ a N D side c z w/gaugeProduct τ hτ a N D side b z w := by
  change ComplexOpenPointEvaluation318.evaluation _ p (FrameScalarAlgebra318.scalar _ _).val=_
  simp only [frame,threeFrame,pairFrame,TensorLineCocycle318.scalar_product,Units.val_mul,map_mul]
  rw [pulled_scalar τ hτ a N D _ b c p z w hp,pulled_scalar τ hτ a N D _ b c p z w hp,
    pulled_scalar τ hτ a N D _ b c p z w hp]
  simp only [gaugeProduct,mul_div_mul_comm,div_pow]
end PELOriginalRosatiProductFrames318
