module
public import PELQuaternionQuadraticCarrier318
public section
noncomputable section
namespace PELQuaternionIntegralInvariants318
open PELQuaternionAlgebra318 PELQuaternionQuadraticCarrier318 QuaternionAlgebra
set_option maxHeartbeats 1000000

theorem scalar_invariants (q : ℚ) (h : IsIntegral ℤ (algebraMap ℚ B q)) :
    (∃ n : ℤ,reducedTrace (algebraMap ℚ B q)=(n:ℚ)) ∧
    (∃ n : ℤ,reducedNorm (algebraMap ℚ B q)=(n:ℚ)) := by
  have hinj : Function.Injective (algebraMap ℚ B) := by
    intro a b h
    simpa [QuaternionAlgebra.algebraMap_eq] using congrArg QuaternionAlgebra.re h
  have hi : IsIntegral ℤ q :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ B) hinj).mp h
  obtain ⟨n,hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  have hq : q=(n:ℚ) := hn.symm
  rw [hq]
  constructor
  · refine ⟨2*n,?_⟩
    simp [reducedTrace,QuaternionAlgebra.algebraMap_eq]
  · refine ⟨n^2,?_⟩
    simp [reducedNorm,QuaternionAlgebra.algebraMap_eq]

/-- Every integral element of the concrete quaternion algebra has integral
reduced trace and norm. The only use of closure of integral elements occurs
inside the explicitly constructed commutative quadratic carrier. -/
theorem invariants (x : B) (h : IsIntegral ℤ x) :
    (∃ n : ℤ,reducedTrace x=(n:ℚ)) ∧ (∃ n : ℤ,reducedNorm x=(n:ℚ)) := by
  by_cases hx : x.imI≠0 ∨ x.imJ≠0 ∨ x.imK≠0
  · have hi := generator_integral x hx h
    have ht := PELQuadraticIntegralInvariants318.trace_integral
      (-reducedNorm x) (reducedTrace x) QuadraticAlgebra.omega hi
    have hn := PELQuadraticIntegralInvariants318.norm_integral
      (-reducedNorm x) (reducedTrace x) QuadraticAlgebra.omega hi
    constructor
    · simpa only [QuadraticAlgebra.trace_omega] using ht
    · simpa [QuadraticAlgebra.norm_def,QuadraticAlgebra.omega] using hn
  · push_neg at hx
    have he : x=algebraMap ℚ B x.re := by
      ext <;> simp [QuaternionAlgebra.algebraMap_eq,hx.1,hx.2.1,hx.2.2]
    rw [he] at h ⊢
    exact scalar_invariants x.re h
end PELQuaternionIntegralInvariants318
