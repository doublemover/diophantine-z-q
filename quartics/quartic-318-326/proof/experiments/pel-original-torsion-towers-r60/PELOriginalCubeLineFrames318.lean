module
public import PELOriginalCubeRegularCoefficients318
public section
noncomputable section
namespace PELOriginalCubeLineFrames318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318 PELOriginalMixedRatioCover318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318 PELOriginalCubeSchemeMaps318
open PELOriginalCubeOpenCover318 PELOriginalCubeBasisCoefficients318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (4*N)] (D : Data τ hτ N)
abbrev pulled (t : Fin 11) := (Scheme.Modules.pullback (maps τ hτ t)).obj D.lineData.M
@[expose] def pulledFrame (t : Fin 11) (b : PELOriginalCubeOpenCover318.Index τ hτ) :
    SheafOfModules.unit (chart τ hτ b).toScheme.ringCatSheaf ≅
      (pulled τ hτ N D t).restrict (chart τ hτ b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (maps τ hτ t) D.lineData.M (opens τ hτ (b t))
      (D.lineData.frame (b t))) (chart τ hτ b) (chart_le τ hτ b t)
@[expose] def positions (side : Bool) : Fin 4 → Fin 11 := if side then ![3,0,1,2] else ![4,5,6,7]
abbrev pairSheaf (side : Bool) := IntrinsicTensorSheaf318.tensor
  (pulled τ hτ N D (positions side 0)) (pulled τ hτ N D (positions side 1))
abbrev threeSheaf (side : Bool) := IntrinsicTensorSheaf318.tensor (pairSheaf τ hτ N D side)
  (pulled τ hτ N D (positions side 2))
abbrev sheaf (side : Bool) := IntrinsicTensorSheaf318.tensor (threeSheaf τ hτ N D side)
  (pulled τ hτ N D (positions side 3))
@[expose] def pairFrame (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ b)
    (pulledFrame τ hτ N D (positions side 0) b) (pulledFrame τ hτ N D (positions side 1) b)
@[expose] def threeFrame (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ b) (pairFrame τ hτ N D side b)
    (pulledFrame τ hτ N D (positions side 2) b)
@[expose] def frame (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ b) (threeFrame τ hτ N D side b)
    (pulledFrame τ hτ N D (positions side 3) b)

lemma pulled_scalar (t : Fin 11) (b c : PELOriginalCubeOpenCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b ⊓ chart τ hτ c).toScheme) (x y z : ComplexVectors)
    (hp : p≫(chart τ hτ b ⊓ chart τ hτ c).ι=triple τ hτ
      (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (pulled τ hτ N D t) (chart τ hτ)
        (pulledFrame τ hτ N D t)).transition b c).val=
      D.lineData.g (c t) (argument x y z t)/D.lineData.g (b t) (argument x y z t) := by
  let W := chart τ hτ b ⊓ chart τ hτ c
  have hm : W≤maps τ hτ t ⁻¹ᵁ (opens τ hτ (b t) ⊓ opens τ hτ (c t)) :=
    fun x hx => ⟨chart_le τ hτ b t hx.1,chart_le τ hτ c t hx.2⟩
  have he : p≫W.ι≫maps τ hτ t=candidateComplexPoint τ hτ (projection (P τ) (argument x y z t)) := by
    rw [←Category.assoc,hp,point_action]
  change ComplexOpenPointEvaluation318.evaluation W p (FrameScalarAlgebra318.scalar _ _).val=_
  simp only [pulledFrame,OpenLineFrameRefinement318.coordinates]
  exact PELOriginalProductLineScalarEvaluation318.scalar_value τ hτ D.lineData
    (maps τ hτ t) (b t) (c t) W hm p (argument x y z t) he
@[expose] def gaugeProduct (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) (x y z : ComplexVectors) : ℂ :=
  D.lineData.g (b (positions side 0)) (argument x y z (positions side 0))*
    D.lineData.g (b (positions side 1)) (argument x y z (positions side 1))*
    D.lineData.g (b (positions side 2)) (argument x y z (positions side 2))*
    D.lineData.g (b (positions side 3)) (argument x y z (positions side 3))
lemma transition_value (side : Bool) (b c : PELOriginalCubeOpenCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b ⊓ chart τ hτ c).toScheme) (x y z : ComplexVectors)
    (hp : p≫(chart τ hτ b ⊓ chart τ hτ c).ι=triple τ hτ
      (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (sheaf τ hτ N D side) (chart τ hτ)
        (frame τ hτ N D side)).transition b c).val=
      gaugeProduct τ hτ N D side c x y z/gaugeProduct τ hτ N D side b x y z := by
  change ComplexOpenPointEvaluation318.evaluation _ p (FrameScalarAlgebra318.scalar _ _).val=_
  simp only [frame,threeFrame,pairFrame,TensorLineCocycle318.scalar_product,Units.val_mul,map_mul]
  rw [pulled_scalar τ hτ N D _ b c p x y z hp,pulled_scalar τ hτ N D _ b c p x y z hp,
    pulled_scalar τ hτ N D _ b c p x y z hp,pulled_scalar τ hτ N D _ b c p x y z hp]
  simp only [gaugeProduct,mul_div_mul_comm]
end PELOriginalCubeLineFrames318
