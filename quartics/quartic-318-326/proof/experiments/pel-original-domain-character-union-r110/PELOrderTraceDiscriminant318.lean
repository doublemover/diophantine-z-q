module
public import PELPrincipalOrderPerfect318
public import PELQuaternionDivision318
public section
noncomputable section
namespace PELOrderTraceDiscriminant318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318
set_option maxHeartbeats 1000000

/-- This is the reduced-trace Gram of the very same integral order used by
the perfect alternating form and the period lattice. -/
@[expose] def traceGram : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => reducedTrace (embed (basis i)*embed (basis j))

theorem traceGram_value : traceGram =
    !![2,0,1,0; 0,-420,0,-210; 1,0,3,0; 0,-210,0,-84] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceGram,reducedTrace,embed,basis,Pi.single_apply]

/-- Exact signed determinant; taking its square root alone does not identify
the local ramification set or prove the order maximal. -/
theorem traceGram_det : Matrix.det traceGram = -(210:ℚ)^2 := by
  rw [traceGram_value]
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,
    Matrix.submatrix_apply,
    show Fin.succAbove (2:Fin 4) (2:Fin 3)=3 from by decide,
    show Fin.succAbove (1:Fin 4) (2:Fin 3)=3 from by decide,
    show Fin.succAbove (3:Fin 4) (2:Fin 3)=2 from by decide]

/-- The alternating Gram on that identical lattice is unimodular. Perfectness
itself is already proved by the explicit dual-vector theorem, not inferred
here from a determinant with an unspecified basis. -/
@[expose] def alternatingGram : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => integralForm (basis i) (basis j)

theorem alternatingGram_value : alternatingGram =
    !![0,-2,0,-1; 2,0,1,0; 0,-1,0,0; 1,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [alternatingGram,integralForm,basis,Pi.single_apply]

theorem alternatingGram_det : Matrix.det alternatingGram=1 := by
  rw [alternatingGram_value]
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three,Fin.sum_univ_succ,
    Matrix.submatrix_apply,
    show Fin.succAbove (2:Fin 4) (2:Fin 3)=3 from by decide,
    show Fin.succAbove (1:Fin 4) (2:Fin 3)=3 from by decide,
    show Fin.succAbove (3:Fin 4) (2:Fin 3)=2 from by decide]
end PELOrderTraceDiscriminant318
