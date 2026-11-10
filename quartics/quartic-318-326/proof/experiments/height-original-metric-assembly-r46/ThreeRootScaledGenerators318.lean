module
public import IntegralOverlapChartMaps318
public import ThreeRootCoordinates318
public section
noncomputable section
namespace ThreeRootScaledGenerators318
open QuadraticPresentation318 ThreeRootCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [CommRing S]

theorem root_scale_smul (a b : S) (y : Sˣ) (ha : IsUnit a) (h : b=a*(y:S)^2) :
    IntegralReciprocalRootScale318.rootEquiv a b y ha h (AdjoinRoot.root (polynomial b))=
      (y:S) • AdjoinRoot.root (polynomial a) := by
  rw [IntegralReciprocalRootScale318.rootEquiv_root,Algebra.smul_def]

/-- Every individual original root has the same signed scaling law in the
actual threefold tensor order. No root permutation or sign quotient is used. -/
theorem order_scale (a b : Fin 3 → S) (y : Sˣ) (ha : ∀ j,IsUnit (a j))
    (h : ∀ j,b j=a j*(y:S)^2) (j : Fin 3) :
    IntegralReciprocalRootScale318.orderEquiv a b y ha h (generator b j)=
      (y:S) • generator a j := by
  fin_cases j <;>
    simp only [IntegralReciprocalRootScale318.orderEquiv,generator,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,map_one,
      root_scale_smul,←TensorProduct.smul_tmul',TensorProduct.tmul_smul]

/-- Parameter transport fixes the literal root generators, not merely their
squares or the rank of the underlying module. -/
theorem parameter_generator (a b : Fin 3 → S) (h : ∀ j,a j=b j) (j : Fin 3) :
    IntegralReciprocalRootScale318.orderParameterEquiv a b h (generator a j)=generator b j := by
  fin_cases j <;>
    simp [IntegralReciprocalRootScale318.orderParameterEquiv,generator,
      Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
end ThreeRootScaledGenerators318
