module
public import PELOriginalOrderPolarizationGauge318
public import PELOriginalBalancedHyperplaneSquares318
public import LineClassPullbackGroup318
public section
noncomputable section
namespace PELOriginalOrderHyperplanePowers318
open AlgebraicGeometry CategoryTheory LineSheafClass318 PELPrincipalOrderCoordinates318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalComplementaryOrder318 PELOriginalOrderPolarizationData318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def cubicData : Data τ hτ where
  lineData := PELOriginalBalancedHyperplaneSquares318.cubicData τ hτ
  coefficient a i j k := PELOriginalOrderPowerCoefficients318.coefficient τ hτ 3 a i.val.1 j.val.1 k
  coefficient_value := PELOriginalOrderPowerCoefficients318.cubic_value τ hτ
@[expose] def quadraticData : Data τ hτ where
  lineData := PELOriginalBalancedHyperplaneSquares318.quadraticData τ hτ
  coefficient a i j k := PELOriginalOrderPowerCoefficients318.coefficient τ hτ 2 a i.val.2 j.val.2 k
  coefficient_value := PELOriginalOrderPowerCoefficients318.quadratic_value τ hτ
@[expose] def source (a : order) (M : Line (candidate τ hτ)) : Line (candidate τ hτ) :=
  LineSheafTensor318.line
    (LineSheafPullback318.line (act τ hτ a) (LineSheafTensorPower318.line M 2))
    (LineSheafPullback318.line (act τ hτ (complement a)) (LineSheafTensorPower318.line M 2))
@[expose] def cubicIso (a : order) :
    (source τ hτ a (cubicLine τ hτ)).object ≅
      (LineSheafTensorPower318.line (cubicLine τ hτ) (2*degree a)).object :=
  PELOriginalOrderPolarizationGauge318.iso τ hτ (cubicData τ hτ) a
@[expose] def quadraticIso (a : order) :
    (source τ hτ a (quadraticLine τ hτ)).object ≅
      (LineSheafTensorPower318.line (quadraticLine τ hτ) (2*degree a)).object :=
  PELOriginalOrderPolarizationGauge318.iso τ hτ (quadraticData τ hτ) a

/-- The defect is a homomorphism of actual whole-line isomorphism
classes. The weight is the explicitly computed integer Hermitian weight,
not an asserted degree of the algebraic endomorphism. -/
@[expose] def defect (a : order) : Class (candidate τ hτ) →* Class (candidate τ hτ) where
  toFun c := LineClassPullbackGroup318.hom (act τ hτ a) c *
    LineClassPullbackGroup318.hom (act τ hτ (complement a)) c * (c^degree a)⁻¹
  map_one' := by simp
  map_mul' c d := by
    simp only [map_mul,mul_pow,mul_inv_rev]
    ac_rfl
lemma defect_square (a : order) (M : Line (candidate τ hτ))
    (e : (source τ hτ a M).object ≅ (LineSheafTensorPower318.line M (2*degree a)).object) :
    (defect τ hτ a (classOf M))^2=1 := by
  have he := classOf_eq e
  change classOf (source τ hτ a M)=classOf (LineSheafTensorPower318.line M (2*degree a)) at he
  simp only [source,LineSheafClassGroup318.classOf_tensor] at he
  change LineClassPullbackGroup318.hom (act τ hτ a)
      (classOf (LineSheafTensorPower318.line M 2))*
    LineClassPullbackGroup318.hom (act τ hτ (complement a))
      (classOf (LineSheafTensorPower318.line M 2))=_ at he
  simp only [LineSheafTensorPower318.classOf_power,map_pow] at he
  change (_*_*(_^degree a)⁻¹)^2=1
  rw [mul_pow,mul_pow,inv_pow,←pow_mul,Nat.mul_comm (degree a) 2,he]
  exact mul_inv_cancel _
lemma cubic_defect (a : order) : (defect τ hτ a (classOf (cubicLine τ hτ)))^2=1 :=
  defect_square τ hτ a _ (cubicIso τ hτ a)
lemma quadratic_defect (a : order) : (defect τ hτ a (classOf (quadraticLine τ hτ)))^2=1 :=
  defect_square τ hτ a _ (quadraticIso τ hτ a)
end PELOriginalOrderHyperplanePowers318
