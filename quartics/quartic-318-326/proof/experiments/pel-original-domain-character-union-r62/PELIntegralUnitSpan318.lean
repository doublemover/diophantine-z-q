module
public import PELGlobalNormOneLevelLifts318
public section
noncomputable section
namespace PELIntegralUnitSpan318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318
set_option maxHeartbeats 1200000

/-- Five already constructed actual global units span the ENTIRE original
order overZ. The norm-minus-one unit is deliberately included. -/
@[expose] def unit : Fin 5 → orderˣ :=
  ![1,PELGlobalIntegralUnitLifts318.generator 0,PELInertiaFivefoldRelation318.residualUnit,
    PELInertiaPrimeWord318.connectingUnit 0,PELGlobalIntegralUnitLifts318.generator 1]
@[expose] def coefficients : Fin 5 → Coordinates :=
  ![![1,0,0,0],![0,0,1,0],![13,-2,13,4],![191,-73,-39,105],![-44,10,15,-15]]

theorem unit_value (j : Fin 5) : ((unit j:order):B)=embed (coefficients j) := by
  fin_cases j
  · change (1:B)=embed ![1,0,0,0]
    ext <;> norm_num [embed]
  · rfl
  · rfl
  · rfl
  · rfl

/-- The exact integer reconstruction, not just a rational basis or rank
argument. In particular there is no hidden denominator at5. -/
@[expose] def expansion (i : Fin 4) : Fin 5 → ℤ :=
  ![![1,0,0,0,0],![332,-453,15,3,25],![0,1,0,0,0],![441,-586,19,4,33]] i

theorem basis_expansion (i : Fin 4) :
    PELPrincipalOrderPerfect318.basis i=
      expansion i 0 • coefficients 0+expansion i 1 • coefficients 1+
      expansion i 2 • coefficients 2+expansion i 3 • coefficients 3+
      expansion i 4 • coefficients 4 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [PELPrincipalOrderPerfect318.basis,expansion,coefficients]

theorem unit_norm (j : Fin 5) : reducedNorm ((unit j:order):B)=1 ∨
    reducedNorm ((unit j:order):B)= -1 := by
  rw [unit_value]
  fin_cases j <;> norm_num [coefficients,embed,reducedNorm]
end PELIntegralUnitSpan318
