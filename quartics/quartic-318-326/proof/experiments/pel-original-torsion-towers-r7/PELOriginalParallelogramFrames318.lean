module
public import PELOriginalParallelogramCover318
public section
noncomputable section
namespace PELOriginalParallelogramFrames318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318 PELOriginalCandidateComplexPoints318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalUniversalBalancedCoefficients318 PELOriginalParallelogramCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (2*N)]
variable (D : PELOriginalUniversalBalancedCoefficients318.Data τ hτ N)
abbrev pulled (t : Fin 4) := (Scheme.Modules.pullback (maps τ hτ t)).obj D.lineData.M
@[expose] def pulledFrame (t : Fin 4) (b : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ b).toScheme.ringCatSheaf ≅
      (pulled τ hτ N D t).restrict (chart τ hτ b).ι :=
  OpenLineFrameRefinement318.frame _ _
    (LinePullbackFrames318.frame (maps τ hτ t) D.lineData.M
      (opens τ hτ (b t)) (D.lineData.frame (b t))) (chart τ hτ b) (chart_le τ hτ b t)
abbrev productSheaf := IntrinsicTensorSheaf318.tensor (pulled τ hτ N D 0) (pulled τ hτ N D 1)
abbrev sourceSheaf := FramedLineTensorPower318.object (productSheaf τ hτ N D) 2
abbrev targetSheaf := IntrinsicTensorSheaf318.tensor (pulled τ hτ N D 2) (pulled τ hτ N D 3)
@[expose] def productFrame (b : Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ b) (pulledFrame τ hτ N D 0 b) (pulledFrame τ hτ N D 1 b)
@[expose] def sourceFrame (b : Index τ hτ) :=
  FramedLineTensorPower318.frames (productSheaf τ hτ N D) (chart τ hτ)
    (productFrame τ hτ N D) 2 b
@[expose] def targetFrame (b : Index τ hτ) :=
  TensorLineLocalFrame318.frame _ _ (chart τ hτ b) (pulledFrame τ hτ N D 2 b) (pulledFrame τ hτ N D 3 b)

lemma pulled_scalar (t : Fin 4) (b c : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b ⊓ chart τ hτ c).toScheme)
    (z a : ComplexVectors)
    (hp : p≫(chart τ hτ b ⊓ chart τ hτ c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (pulled τ hτ N D t) (chart τ hτ)
        (pulledFrame τ hτ N D t)).transition b c).val=
      D.lineData.g (c t) (argument z a t)/D.lineData.g (b t) (argument z a t) := by
  let W := chart τ hτ b ⊓ chart τ hτ c
  have hm : W≤maps τ hτ t ⁻¹ᵁ (opens τ hτ (b t) ⊓ opens τ hτ (c t)) :=
    fun x hx => ⟨chart_le τ hτ b t hx.1,chart_le τ hτ c t hx.2⟩
  have he : p≫W.ι≫maps τ hτ t=candidateComplexPoint τ hτ (projection (P τ) (argument z a t)) := by
    rw [←Category.assoc,hp,point_action]
  change ComplexOpenPointEvaluation318.evaluation W p (FrameScalarAlgebra318.scalar _ _).val=_
  simp only [pulledFrame,OpenLineFrameRefinement318.coordinates]
  exact PELOriginalProductLineScalarEvaluation318.scalar_value τ hτ D.lineData
    (maps τ hτ t) (b t) (c t) W hm p (argument z a t) he

lemma source_transition_value (b c : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b ⊓ chart τ hτ c).toScheme)
    (z a : ComplexVectors)
    (hp : p≫(chart τ hτ b ⊓ chart τ hτ c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (sourceSheaf τ hτ N D) (chart τ hτ)
        (sourceFrame τ hτ N D)).transition b c).val=
      ((D.lineData.g (c 0) z/D.lineData.g (b 0) z)*
        (D.lineData.g (c 1) a/D.lineData.g (b 1) a))^2 := by
  rw [sourceFrame,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val,map_pow]
  congr 1
  change ComplexOpenPointEvaluation318.evaluation _ p (FrameScalarAlgebra318.scalar _ _).val=_
  rw [TensorLineCocycle318.scalar_product,Units.val_mul,map_mul]
  rw [pulled_scalar τ hτ N D 0 b c p z a hp,pulled_scalar τ hτ N D 1 b c p z a hp]
  rfl

lemma target_transition_value (b c : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b ⊓ chart τ hτ c).toScheme)
    (z a : ComplexVectors)
    (hp : p≫(chart τ hτ b ⊓ chart τ hτ c).ι=pair τ hτ (projection (P τ) z) (projection (P τ) a)) :
    ComplexOpenPointEvaluation318.evaluation _ p
      ((LineFrameCocycle318.cocycle (targetSheaf τ hτ N D) (chart τ hτ)
        (targetFrame τ hτ N D)).transition b c).val=
      (D.lineData.g (c 2) (z+a)/D.lineData.g (b 2) (z+a))*
        (D.lineData.g (c 3) (z-a)/D.lineData.g (b 3) (z-a)) := by
  change ComplexOpenPointEvaluation318.evaluation _ p (FrameScalarAlgebra318.scalar _ _).val=_
  rw [TensorLineCocycle318.scalar_product,Units.val_mul,map_mul]
  rw [pulled_scalar τ hτ N D 2 b c p z a hp,pulled_scalar τ hτ N D 3 b c p z a hp]
  rfl
end PELOriginalParallelogramFrames318
