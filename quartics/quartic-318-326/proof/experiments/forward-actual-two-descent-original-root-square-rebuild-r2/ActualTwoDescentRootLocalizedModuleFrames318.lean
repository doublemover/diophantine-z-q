module
public import ActualTwoDescentPrincipalIdealModuleFrame318
public section
noncomputable section
open scoped TensorProduct
namespace ActualTwoDescentRootLocalizedModuleFrames318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentPrincipalIdealModuleFrame318
variable {K : Type*} [Field K] [CharZero K]

instance rootChartDomain (n : K) (i : Fin 3) (b : Bool) : IsDomain (RootChartRing n i b) :=
  IsLocalization.Away.isDomain _ (actual_root_chart_denominator_nonzero n i b)
def rootLocalGenerator (n : K) (i : Fin 3) : (b : Bool) → RootChartRing n i b
  | false => 1
  | true => rootChartMap n i true (affineY n)
lemma actual_root_local_generator_nonzero (n : K) (i : Fin 3) (b : Bool) :
    rootLocalGenerator n i b≠0 := by
  cases b
  · exact one_ne_zero
  · intro h
    apply actual_affine_y_nonzero n
    apply actual_root_chart_injective n i true
    simpa only [map_zero] using h
lemma actual_root_local_generator_ideal (n : K) (i : Fin 3) (b : Bool) :
    localizedRootIdeal n i b=Ideal.span {rootLocalGenerator n i b} := by
  cases b
  · rw [actual_root_complement_unit_ideal]
    simp [rootLocalGenerator]
  · exact actual_root_branch_principal n i

/-- Both actual extended root-ideal modules are explicitly free of
rank one. On the root chart the frame is y, not an assumed unit y. -/
def rootLocalFrame (n : K) (i : Fin 3) (b : Bool) :
    RootChartRing n i b ≃ₗ[RootChartRing n i b] localizedRootIdeal n i b :=
  principalModuleFrame _ _ (actual_root_local_generator_ideal n i b)
    (actual_root_local_generator_nonzero n i b)
@[simp] lemma actual_root_local_frame_value (n : K) (i : Fin 3) (b : Bool)
    (a : RootChartRing n i b) :
    (rootLocalFrame n i b a : RootChartRing n i b)=a*rootLocalGenerator n i b := rfl

/-- The native tensor square of the actual ideal module, with its
coefficient in the tensor product of the two specified actual frames. -/
def rootTensorFrame (n : K) (i : Fin 3) (b : Bool) :
    (localizedRootIdeal n i b) ⊗[RootChartRing n i b] (localizedRootIdeal n i b)
      ≃ₗ[RootChartRing n i b] RootChartRing n i b :=
  (TensorProduct.congr (rootLocalFrame n i b).symm (rootLocalFrame n i b).symm).trans
    (TensorProduct.lid _ _)
lemma actual_root_tensor_frame (n : K) (i : Fin 3) (b : Bool)
    (a c : RootChartRing n i b) :
    rootTensorFrame n i b (rootLocalFrame n i b a ⊗ₜ[RootChartRing n i b]
      rootLocalFrame n i b c)=a*c := by
  simp [rootTensorFrame,TensorProduct.congr_tmul,TensorProduct.lid_tmul]
end ActualTwoDescentRootLocalizedModuleFrames318
