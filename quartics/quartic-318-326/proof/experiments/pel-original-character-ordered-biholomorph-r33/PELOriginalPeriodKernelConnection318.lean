module
public import PELOriginalFlatPeriodKernel318
public import PELOriginalPeriodBilinear318
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public section
noncomputable section
namespace PELOriginalPeriodKernelConnection318
open QuaternionicRealPeriod318 PELQuaternionRealRepresentation318
open PELOriginalSiegelNormalization318 PELOriginalPeriodMatrixDerivative318
open PELOriginalFlatPeriodKernel318 PELOriginalPeriodBilinear318

lemma hasDerivAt_period_evaluation (τ : ℂ) (hτ : τ≠0) (v : ComplexVectors) :
    HasDerivAt (fun z => (PELOriginalSiegelMatrix318.omega z).mulVec v)
      ((derivative τ).mulVec v) τ := by
  exact (evaluation v).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ
    (hasDerivAt_omega τ hτ)

/-- The ordinary flat derivative in the fixed complexified original
integral-period space. This is an actual derivative of a kernel frame,
not an unspecified connection coefficient. -/
lemma hasDerivAt_kernelLift (τ : ℂ) (hτ : τ≠0) (v : ComplexVectors) :
    HasDerivAt (fun z => kernelLift z v) (-(derivative τ).mulVec v,0) τ := by
  exact (hasDerivAt_period_evaluation τ hτ v).neg.prodMk (hasDerivAt_const τ v)

/-- Whole normal-class operator obtained by differentiating the actual
period-kernel frame and applying the actual period quotient map. -/
@[expose] def normalDerivative (τ : ℂ) (v : ComplexVectors) : ComplexVectors :=
  periodMap τ (deriv (fun z => kernelLift z v) τ)
lemma normalDerivative_formula (τ : ℂ) (hτ : τ≠0) (v : ComplexVectors) :
    normalDerivative τ v= -(derivative τ).mulVec v := by
  unfold normalDerivative
  rw [(hasDerivAt_kernelLift τ hτ v).deriv]
  simp [periodMap]

/-- The actual standard alternating pairing in the original ordered
symplectic coordinates, extended to the whole complex vector space. -/
@[expose] def symplectic (p q : Ambient) : ℂ :=
  dotProduct p.1 q.2-dotProduct p.2 q.1
lemma symplectic_integral (p q : PELOriginalSymplecticCoordinates318.Pair) :
    symplectic (integralVector p) (integralVector q)=
      (PELOriginalSymplecticCoordinates318.standard p q:ℂ) := by
  simp [symplectic,integralVector,dotProduct,Fin.sum_univ_two,
    PELOriginalSymplecticCoordinates318.standard]
  push_cast
  ring
lemma symplectic_original (p q : PELOriginalSymplecticCoordinates318.Pair) :
    symplectic (integralVector p) (integralVector q)=
      ((-PELPrincipalOrderCoordinates318.integralForm
        (PELOriginalSymplecticCoordinates318.fromPair p)
        (PELOriginalSymplecticCoordinates318.fromPair q)):ℂ) := by
  rw [symplectic_integral,PELOriginalSymplecticCoordinates318.exact_form_pair]

/-- The actual whole period-kernel plane is isotropic for the original
polarization form, not merely a rank-two subspace with a chosen pairing. -/
lemma kernel_isotropic (τ : ℂ) (v w : ComplexVectors) :
    symplectic (kernelLift τ v) (kernelLift τ w)=0 := by
  simp [symplectic,kernelLift,dotProduct,Matrix.mulVec,Fin.sum_univ_two,
    PELOriginalSiegelMatrix318.omega]
  ring
@[expose] def secondPairing (τ : ℂ) (v w : ComplexVectors) : ℂ :=
  symplectic (kernelLift τ v) (deriv (fun z => kernelLift z w) τ)
lemma secondPairing_formula (τ : ℂ) (hτ : τ≠0) (v w : ComplexVectors) :
    secondPairing τ v w=dotProduct v ((derivative τ).mulVec w) := by
  unfold secondPairing
  rw [(hasDerivAt_kernelLift τ hτ w).deriv]
  simp [symplectic,kernelLift,dotProduct,Fin.sum_univ_two]
  ring

/-- Both genuine kernel vectors are transformed by the TRANSPOSE of the
actual a-period matrix, giving the already proved original congruence.
This retains the sign of the actual kernel lift and alternating pairing. -/
lemma original_secondPairing (τ : ℂ) (hτ : τ≠0) (z w : ComplexVectors) :
    secondPairing τ ((originalMatrix τ).transpose.mulVec z)
      ((originalMatrix τ).transpose.mulVec w)=
      (alpha:ℂ)*(z 0*w 0+z 1*w 1) := by
  rw [secondPairing_formula τ hτ]
  have he : dotProduct ((originalMatrix τ).transpose.mulVec z)
      ((derivative τ).mulVec ((originalMatrix τ).transpose.mulVec w))=
      pairing τ z w := by
    simp [pairing,dotProduct,Matrix.mulVec,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_two]
    ring
  rw [he,pairing_formula τ hτ]
end PELOriginalPeriodKernelConnection318
