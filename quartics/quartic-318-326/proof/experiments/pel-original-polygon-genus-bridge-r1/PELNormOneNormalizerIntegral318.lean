module
public import PELNormalizerTraceIntegral318
public section
noncomputable section
namespace PELNormOneNormalizerIntegral318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELActualOrderNormalizer318
open PELQuaternionNormParity318 PELNormalizerTraceIntegral318 PELIntegralUnitSpan318
set_option maxHeartbeats 1600000

theorem trace_basis_expansion (x : B) (i : Fin 4) :
    reducedTrace (x*embed (PELPrincipalOrderPerfect318.basis i))=
      (expansion i 0:ℚ)*reducedTrace (x*embed (coefficients 0))+
      (expansion i 1:ℚ)*reducedTrace (x*embed (coefficients 1))+
      (expansion i 2:ℚ)*reducedTrace (x*embed (coefficients 2))+
      (expansion i 3:ℚ)*reducedTrace (x*embed (coefficients 3))+
      (expansion i 4:ℚ)*reducedTrace (x*embed (coefficients 4)) := by
  fin_cases i <;>
    norm_num [PELPrincipalOrderPerfect318.basis,expansion,coefficients,embed,reducedTrace]
  all_goals ring

/-- The entire original trace dual is reached using genuine original
integral UNIT tests, because the five specified units spanO overZ. -/
theorem all_trace_tests (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    ∀ i : Fin 4,∃ z : ℤ,reducedTrace ((u.val:B)*embed (PELPrincipalOrderPerfect318.basis i))=(z:ℚ) := by
  have hj (j : Fin 5) : ∃ z : ℤ,reducedTrace ((u.val:B)*embed (coefficients j))=(z:ℚ) := by
    let w : normalizer := ⟨u.val*integralUnit (unit j),normalizer.mul_mem u.property (integral_mem _)⟩
    have hw : reducedNorm (w.val:B)=1 ∨ reducedNorm (w.val:B)= -1 := by
      change reducedNorm ((u.val:B)*((unit j:order):B))=1 ∨ _
      rw [norm_mul,hu,one_mul]
      exact unit_norm j
    obtain ⟨z,hz⟩ := norm_sign_trace_integral w hw
    refine ⟨z,?_⟩
    change reducedTrace ((u.val:B)*((unit j:order):B))=(z:ℚ) at hz
    rw [unit_value] at hz
    exact hz
  choose z hz using hj
  intro i
  refine ⟨expansion i 0*z 0+expansion i 1*z 1+expansion i 2*z 2+
    expansion i 3*z 3+expansion i 4*z 4,?_⟩
  rw [trace_basis_expansion,hz 0,hz 1,hz 2,hz 3,hz 4]
  push_cast <;> ring

/-- A norm-one rational normalizer is genuinely IN the original order.
The final membership is the previously proved explicit trace-dual/norm
saturation, not a local maximal-order classification supplied as an axiom. -/
theorem norm_one_mem_order (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    (u.val:B)∈order :=
  PELTraceDualSaturation318.mem_of_integral_trace_norm (u.val:B)
    (all_trace_tests u hu) ⟨1,by simpa using hu⟩

theorem inverse_norm_one (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    reducedNorm ((u⁻¹).val:B)=1 := by
  have h := norm_mul (u.val:B) (↑u.val⁻¹:B)
  rw [Units.val_inv] at h
  have h1 : reducedNorm (1:B)=1 := by norm_num [reducedNorm]
  rw [h1,hu,one_mul] at h
  exact h.symm

/-- Both original integral memberships are proved, so the result is an
actual integral UNIT with the original inverse and norm. -/
@[expose] def integralUnitOfNormOne (u : normalizer) (hu : reducedNorm (u.val:B)=1) : orderˣ where
  val := ⟨(u.val:B),norm_one_mem_order u hu⟩
  inv := ⟨(↑u.val⁻¹:B),norm_one_mem_order u⁻¹ (inverse_norm_one u hu)⟩
  val_inv := Subtype.ext (Units.val_inv u.val)
  inv_val := Subtype.ext (Units.inv_val u.val)

theorem integralUnitOfNormOne_value (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    integralUnit (integralUnitOfNormOne u hu)=u.val := by
  apply Units.ext
  rfl

theorem integralUnitOfNormOne_norm (u : normalizer) (hu : reducedNorm (u.val:B)=1) :
    reducedNorm ((integralUnitOfNormOne u hu:order):B)=1 := hu
end PELNormOneNormalizerIntegral318
