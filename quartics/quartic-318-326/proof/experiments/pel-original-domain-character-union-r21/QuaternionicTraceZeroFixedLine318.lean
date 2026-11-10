module
public import PELFineLevelFibers318
public section
noncomputable section
namespace QuaternionicTraceZeroFixedLine318
open QuaternionicRealPeriod318 QuaternionicFixedParameter318
set_option maxHeartbeats 1400000

/-- The trace-zero real endomorphisms fixing one upper-half-plane line
form ONE real line. The full matrix proportionality is explicit. -/
theorem proportional (M N : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (hM : fixesLine M τ) (hN : fixesLine N τ)
    (htM : M 0 0+M 1 1=0) (htN : N 0 0+N 1 1=0)
    (hcN : N 1 0≠0) : M=(M 1 0/N 1 0) • N := by
  obtain ⟨haM,hbM⟩ := coordinate_relations M τ hτ hM
  obtain ⟨haN,hbN⟩ := coordinate_relations N τ hτ hN
  have h00M : M 0 0=M 1 0*τ.re := by linarith
  have h11M : M 1 1= -M 1 0*τ.re := by linarith
  have h00N : N 0 0=N 1 0*τ.re := by linarith
  have h11N : N 1 1= -N 1 0*τ.re := by linarith
  let r : ℝ := M 1 0/N 1 0
  have hr : r*N 1 0=M 1 0 := div_mul_cancel₀ _ hcN
  ext i j
  fin_cases i <;> fin_cases j
  · change M 0 0=r*N 0 0
    rw [h00M,h00N,←mul_assoc,hr]
  · change M 0 1=r*N 0 1
    rw [hbM,hbN,←hr]
    ring
  · change M 1 0=r*N 1 0
    exact hr.symm
  · change M 1 1=r*N 1 1
    rw [h11M,h11N,←hr]
    ring
end QuaternionicTraceZeroFixedLine318
