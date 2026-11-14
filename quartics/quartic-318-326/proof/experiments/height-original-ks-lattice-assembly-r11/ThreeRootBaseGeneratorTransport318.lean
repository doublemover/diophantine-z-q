module
public import IntegralOriginalChartsProperCover318
public section
noncomputable section
namespace ThreeRootBaseGeneratorTransport318
open ThreeRootCoordinates318 ThreeRootBaseEquivalence318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type*} [CommRing A] [CommRing B]

/-- Heterobasic coefficient transport fixes each original root generator
exactly, including its sign and its specified position in the tensor order. -/
theorem three_generator (e : A ≃+* B) (a : Fin 3 → A) (b : Fin 3 → B)
    (h : ∀ i,e (a i)=b i) (j : Fin 3) :
    three e a b h (generator a j)=generator b j := by
  fin_cases j <;>
    simp [three,pair,generator,TensorBaseEquivalence318.equiv_tmul,root_root]
end ThreeRootBaseGeneratorTransport318
