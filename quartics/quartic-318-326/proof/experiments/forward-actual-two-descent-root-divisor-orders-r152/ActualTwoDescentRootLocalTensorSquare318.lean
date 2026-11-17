module
public import ActualTwoDescentRootLocalizedModuleFrames318
public section
noncomputable section
open scoped TensorProduct
namespace ActualTwoDescentRootLocalTensorSquare318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentPrincipalIdealModuleFrame318 ActualTwoDescentRootLocalizedModuleFrames318
variable {K : Type*} [Field K] [CharZero K]

def rootDenominatorUnit (n : K) (i : Fin 3) (b : Bool) : (RootChartRing n i b)ˣ :=
  Units.mkOfMulEqOne (rootChartMap n i b (rootChartElement n i b))
    (rootChartInverse n i b) (actual_root_chart_inverse n i b)
def rootSquareUnit (n : K) (i : Fin 3) : (b : Bool) → (RootChartRing n i b)ˣ
  | false => (rootDenominatorUnit n i false)⁻¹
  | true => rootDenominatorUnit n i true
lemma actual_root_generator_square (n : K) (i : Fin 3) (b : Bool) :
    (rootLocalGenerator n i b)^2=
      rootChartMap n i b (rootNumerator n i)*(rootSquareUnit n i b : RootChartRing n i b) := by
  cases b
  · change (1 : RootChartRing n i false)^2=
      rootChartMap n i false (rootChartElement n i false)*rootChartInverse n i false
    rw [actual_root_chart_inverse,one_pow]
  · exact actual_root_local_equation n i true
lemma actual_local_root_function_nonzero (n : K) (i : Fin 3) (b : Bool) :
    rootChartMap n i b (rootNumerator n i)≠0 := by
  intro h
  apply actual_root_numerator_nonzero n i
  apply actual_root_chart_injective n i b
  simpa only [map_zero] using h

/-- A genuine native tensor-square isomorphism onto the principal ideal
of the SAME original x−a in each chart. It is constructed, not posited. -/
def rootLocalSquareEquiv (n : K) (i : Fin 3) (b : Bool) :
    (localizedRootIdeal n i b) ⊗[RootChartRing n i b] (localizedRootIdeal n i b)
      ≃ₗ[RootChartRing n i b]
        (Ideal.span {rootChartMap n i b (rootNumerator n i)} : Ideal (RootChartRing n i b)) :=
  (rootTensorFrame n i b).trans ((unitScale (rootSquareUnit n i b)).trans
    (principalModuleFrame _ _ rfl (actual_local_root_function_nonzero n i b)))

/-- The local tensor equivalence is EXACT multiplication of the two
actual ideal elements. No unidentified nonzero scalar is suppressed. -/
theorem actual_root_tensor_square_multiplication (n : K) (i : Fin 3) (b : Bool)
    (x y : localizedRootIdeal n i b) :
    (rootLocalSquareEquiv n i b (x ⊗ₜ[RootChartRing n i b] y) : RootChartRing n i b)=
      (x : RootChartRing n i b)*(y : RootChartRing n i b) := by
  obtain ⟨a,rfl⟩ := (rootLocalFrame n i b).surjective x
  obtain ⟨c,rfl⟩ := (rootLocalFrame n i b).surjective y
  change (rootTensorFrame n i b (rootLocalFrame n i b a ⊗ₜ[RootChartRing n i b]
    rootLocalFrame n i b c)*(rootSquareUnit n i b : RootChartRing n i b))*
      rootChartMap n i b (rootNumerator n i)=_
  rw [actual_root_tensor_frame,actual_root_local_frame_value,actual_root_local_frame_value]
  have h := actual_root_generator_square n i b
  linear_combination -a*c*h
end ActualTwoDescentRootLocalTensorSquare318
