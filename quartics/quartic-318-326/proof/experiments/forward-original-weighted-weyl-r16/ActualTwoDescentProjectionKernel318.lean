module
public import ActualTwoDescentZeroSumCompletion318
public section
noncomputable section
namespace ActualTwoDescentProjectionKernel318
open ActualTwoDescentZeroSumCompletion318
open scoped Matrix
set_option maxHeartbeats 16000000

/-- The retained rank-one projection T=Id-v*a, with v the indicator
of the original beta support. This keeps the original correction sign. -/
@[expose] def projectedAction {ι : Type*} [Fintype ι]
    (M : Matrix ι ι (ZMod 2)) (a : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (v x : ι → ZMod 2) : ι → ZMod 2 := M *ᵥ (x-a x • v)

/-- The actual projected kernel is the two-dimensional candidate span
of the constant vector and the beta-support vector. Its two generators are
not inferred from a dimension count or from separate matrix selections. -/
theorem actual_projected_kernel {ι : Type*} [Fintype ι]
    (M : Matrix ι ι (ZMod 2)) (a : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (v : ι → ZMod 2) (ha1 : a (ones ι)=0) (hav : a v=1)
    (h1 : M *ᵥ ones ι=0)
    (hker : ∀ x, M *ᵥ x=0 → ∃ c : ZMod 2, x=c • ones ι)
    (x : ι → ZMod 2) : projectedAction M a v x=0 ↔
      ∃ c d : ZMod 2, x=c • ones ι+d • v := by
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := hker (x-a x • v) hx
    exact ⟨c,a x,eq_add_of_sub_eq hc⟩
  · rintro ⟨c,d,rfl⟩
    have ha : a (c • ones ι+d • v)=d := by simp only [map_add,map_smul,ha1,hav,smul_eq_mul,mul_zero,mul_one,zero_add]
    simp only [projectedAction,ha,add_sub_cancel_right,Matrix.mulVec_smul,h1,smul_zero]

/-- The same construction proves lambda is NOT in the projected image,
which is the second exact linear-algebra condition used by two-descent. -/
theorem actual_lambda_not_image {ι : Type*} [Fintype ι]
    (M : Matrix ι ι (ZMod 2)) (a : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (v : ι → ZMod 2) (ha1 : a (ones ι)=0) (hav : a v=1)
    (hker : ∀ x, M *ᵥ x=0 → ∃ c : ZMod 2, x=c • ones ι) :
    ∀ x, projectedAction M a v x ≠ M *ᵥ v := by
  intro x hx
  have hz : M *ᵥ ((x-a x • v)-v)=0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hx
  obtain ⟨c,hc⟩ := hker _ hz
  have he := congrArg a hc
  simp only [map_sub,map_smul,hav,ha1,smul_eq_mul,mul_one,mul_zero,sub_self,
    zero_sub] at he
  norm_num at he

end ActualTwoDescentProjectionKernel318
