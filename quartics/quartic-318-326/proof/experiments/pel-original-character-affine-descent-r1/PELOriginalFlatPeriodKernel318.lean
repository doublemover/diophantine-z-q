module
public import PELOriginalPeriodMatrixDerivative318
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public section
noncomputable section
namespace PELOriginalFlatPeriodKernel318
open QuaternionicRealPeriod318 PELOriginalSymplecticCoordinates318
open PELOriginalSiegelMatrix318 PELOriginalSiegelNormalization318
open PELOriginalPeriodMatrixDerivative318

abbrev Ambient := ComplexVectors × ComplexVectors
/-- Complex-linear extension of the SAME integral normalized period map. -/
@[expose] def periodMap (τ : ℂ) : Ambient →ₗ[ℂ] ComplexVectors where
  toFun p := p.1+(omega τ).mulVec p.2
  map_add' := by intros; simp [Matrix.mulVec_add]; abel
  map_smul' := by intros; simp [Matrix.mulVec_smul,smul_add]
@[expose] def integralVector (p : Pair) : Ambient :=
  (fun i => (p.1 i:ℂ),fun i => (p.2 i:ℂ))
lemma integral_period (τ : ℂ) (p : Pair) :
    periodMap τ (integralVector p)=standardPeriod τ p := by
  ext i
  simp [periodMap,integralVector,standardPeriod,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring
lemma original_integral_period (τ : ℂ) (hτ : 0<τ.im) (p : Pair) :
    normalization τ hτ (QuaternionicOrderPeriodQuotient318.periodHom
      PELQuaternionRealRepresentation318.representation τ
      (PELPrincipalOrderCoordinates318.embed (fromPair p)))=
      periodMap τ (integralVector p) := by
  rw [integral_period]
  exact original_period τ hτ p

/-- The genuine whole kernel plane of the actual complexified periods. -/
@[expose] def kernelLift (τ : ℂ) : ComplexVectors →ₗ[ℂ] Ambient where
  toFun v := (-(omega τ).mulVec v,v)
  map_add' := by intros; simp [Matrix.mulVec_add,neg_add]
  map_smul' := by intros; simp [Matrix.mulVec_smul,smul_neg]
lemma kernelLift_period (τ : ℂ) (v : ComplexVectors) :
    periodMap τ (kernelLift τ v)=0 := by simp [periodMap,kernelLift]
lemma kernelLift_injective (τ : ℂ) : Function.Injective (kernelLift τ) := by
  intro v w h
  exact congrArg Prod.snd h
lemma kernelLift_range (τ : ℂ) : LinearMap.range (kernelLift τ)=LinearMap.ker (periodMap τ) := by
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    exact kernelLift_period τ v
  · intro hp
    have h : p.1+(omega τ).mulVec p.2=0 := hp
    refine ⟨p.2,?_⟩
    apply Prod.ext
    · exact (eq_neg_of_add_eq_zero_left h).symm
    · rfl
lemma periodMap_surjective (τ : ℂ) : Function.Surjective (periodMap τ) := by
  intro v
  refine ⟨(v,0),?_⟩
  simp [periodMap]

/-- Evaluation on a fixed whole vector is a continuous linear operation
on the finite-dimensional matrix space, for the actual derivative proof. -/
@[expose] def evaluation (v : ComplexVectors) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ComplexVectors where
  toFun M := M.mulVec v
  map_add' := by intros; exact Matrix.add_mulVec _ _ _
  map_smul' := by intros; exact Matrix.smul_mulVec _ _ _
end PELOriginalFlatPeriodKernel318
