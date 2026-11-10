module
public import IntegralBinaryEnergy318
public import PELDirichletSidePairingData318
public section
noncomputable section
namespace PELOriginalVertexEnergy318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318 PELQuaternionKleinAction318
set_option maxHeartbeats 1800000

/-- Explicit integer inverse matrices on the SAME original order basis.
Rows give the new coordinates; no saturation or lattice replacement. -/
@[expose] def inverseMatrix : Fin 28 → Fin 4 → Fin 4 → ℤ := ![
  ![![0,21,1,7],![0,18,1,6],![1,7,0,0],![1,6,0,0]],
  ![![0,21,-1,7],![0,-18,1,-6],![-1,7,0,0],![1,-6,0,0]],
  ![![-1,-63,-4,-21],![-3,-21,-1,0],![0,16,1,6],![1,2,0,-2]],
  ![![1,-63,4,-21],![3,-21,1,0],![0,-16,1,-6],![1,-2,0,2]],
  ![![2,14,1,0],![-1,28,2,14],![1,15,1,3],![0,15,1,6]],
  ![![-2,14,-1,0],![1,28,-2,14],![1,-15,1,-3],![0,-15,1,-6]],
  ![![1,-28,-2,-14],![2,14,1,0],![0,15,1,6],![1,0,0,-3]],
  ![![1,-42,3,-14],![2,-14,1,0],![1,15,-1,9],![1,0,0,3]],
  ![![3,21,2,0],![-1,42,3,21],![1,12,1,2],![0,14,1,6]],
  ![![-3,21,-2,0],![1,42,-3,21],![1,-12,1,-2],![0,-14,1,-6]],
  ![![-2,-63,-5,-21],![-3,-21,-2,0],![0,14,1,6],![1,-2,0,-4]],
  ![![2,-63,5,-21],![3,-21,2,0],![0,-14,1,-6],![1,2,0,4]],
  ![![1,21,2,7],![1,-18,-1,-12],![1,7,1,0],![1,-6,0,-6]],
  ![![0,14,-1,7],![0,-12,1,-6],![1,-7,1,0],![1,6,0,6]],
  ![![0,-14,-1,-7],![0,-12,-1,-6],![-1,7,0,7],![1,6,1,0]],
  ![![-1,-21,1,-14],![1,-18,2,-6],![-1,-7,0,-7],![1,-6,1,0]],
  ![![1,42,4,21],![3,-21,1,-21],![1,16,2,6],![1,2,1,-2]],
  ![![-1,42,-4,21],![-3,-21,-1,-21],![1,-16,2,-6],![1,-2,1,2]],
  ![![4,21,5,0],![1,42,4,21],![1,2,1,-2],![0,14,1,8]],
  ![![-4,21,-5,0],![-1,42,-4,21],![1,-2,1,2],![0,-14,1,-8]],
  ![![-1,42,2,28],![-2,14,-1,14],![1,15,2,6],![1,0,1,-3]],
  ![![-1,28,-3,14],![-2,-14,-1,-14],![0,15,-1,9],![1,0,1,3]],
  ![![3,14,4,0],![1,28,3,14],![1,0,1,-3],![0,15,1,9]],
  ![![-3,14,-4,0],![-1,28,-3,14],![1,0,1,3],![0,-15,1,-9]],
  ![![2,42,5,21],![3,-21,2,-21],![1,14,2,6],![1,-2,1,-4]],
  ![![-2,42,-5,21],![-3,-21,-2,-21],![1,-14,2,-6],![1,2,1,4]],
  ![![-1,-14,-2,-7],![1,12,2,6],![-1,7,-1,7],![1,-6,1,-6]],
  ![![1,-14,2,-7],![1,-12,2,-6],![1,7,1,7],![1,6,1,6]]]
@[expose] def forwardMatrix : Fin 28 → Fin 4 → Fin 4 → ℤ := ![
  ![![0,0,-6,7],![0,0,1,-1],![-6,7,0,0],![1,-1,-3,3]],
  ![![0,0,6,7],![0,0,1,1],![6,7,0,0],![1,1,-3,-3]],
  ![![2,-8,0,-21],![0,1,1,3],![-6,2,-21,0],![1,-3,1,-8]],
  ![![-2,8,0,-21],![0,1,-1,-3],![6,-2,-21,0],![1,-3,-1,8]],
  ![![6,-3,-14,14],![-1,0,2,-1],![3,6,0,-14],![2,-1,-5,5]],
  ![![-6,3,-14,14],![-1,0,-2,1],![-3,-6,0,-14],![2,-1,5,-5]],
  ![![3,6,0,-14],![0,-1,1,2],![-6,3,-14,0],![1,2,0,-5]],
  ![![-3,9,0,-14],![0,1,1,-3],![6,-3,14,-14],![1,-3,0,5]],
  ![![6,-4,-21,21],![-1,0,3,-1],![2,6,0,-21],![2,-1,-7,6]],
  ![![-6,4,-21,21],![-1,0,-3,1],![-2,-6,0,-21],![2,-1,7,-6]],
  ![![4,-10,0,-21],![0,1,2,3],![-6,4,-21,0],![1,-3,-1,-7]],
  ![![-4,10,0,-21],![0,1,-2,-3],![6,-4,-21,0],![1,-3,1,7]],
  ![![6,0,-12,7],![0,1,1,-2],![-6,-7,6,7],![1,-1,-3,3]],
  ![![-6,0,-6,7],![0,1,-1,1],![6,7,0,0],![1,-1,2,-2]],
  ![![0,7,6,7],![-1,0,-1,-1],![6,-7,0,0],![1,1,2,2]],
  ![![0,-7,6,14],![-1,0,2,1],![-6,7,6,-7],![1,1,-3,-3]],
  ![![-2,8,21,-42],![-1,-1,1,3],![6,-2,-21,21],![1,2,1,-8]],
  ![![2,-8,21,-42],![-1,-1,-1,-3],![-6,2,-21,21],![1,2,-1,8]],
  ![![8,-10,-21,21],![-1,0,4,1],![-2,8,0,-21],![2,-1,-7,1]],
  ![![-8,10,-21,21],![-1,0,-4,-1],![2,-8,0,-21],![2,-1,7,-1]],
  ![![-3,-6,14,-28],![-1,2,1,2],![6,-3,-14,14],![1,-3,0,-5]],
  ![![3,-9,-14,-14],![-1,-1,1,-3],![-6,3,14,0],![1,2,0,5]],
  ![![9,-12,-14,14],![-1,0,3,1],![-3,9,0,-14],![2,-1,-5,0]],
  ![![-9,12,-14,14],![-1,0,-3,-1],![3,-9,0,-14],![2,-1,5,0]],
  ![![-4,10,21,-42],![-1,-1,2,3],![6,-4,-21,21],![1,2,-1,-7]],
  ![![4,-10,21,-42],![-1,-1,-2,-3],![-6,4,-21,21],![1,2,1,7]],
  ![![-6,-7,12,14],![-1,-1,-1,-1],![6,7,-6,-7],![1,1,2,2]],
  ![![6,-7,-12,14],![-1,1,-1,1],![-6,7,6,-7],![1,-1,2,-2]]]
@[expose] def kind : Fin 28 → Fin 5 := ![0,0,1,1,2,2,3,3,4,4,1,1,0,0,0,0,1,1,4,4,3,3,2,2,1,1,0,0]
@[expose] def applyMatrix (M : Fin 4 → Fin 4 → ℤ) (x : Coordinates) : Coordinates :=
  fun i => M i 0*x 0+M i 1*x 1+M i 2*x 2+M i 3*x 3
@[expose] def coordinates (v : Fin 28) (x : Coordinates) : Coordinates :=
  applyMatrix (inverseMatrix v) x

/-- Both identities explicitly certify the coordinate change is unimodular. -/
theorem inverse_forward (v : Fin 28) (x : Coordinates) :
    coordinates v (applyMatrix (forwardMatrix v) x)=x ∧
    applyMatrix (forwardMatrix v) (coordinates v x)=x := by
  constructor <;> ext i <;> fin_cases v <;> fin_cases i <;>
    norm_num [coordinates,applyMatrix,inverseMatrix,forwardMatrix] <;> ring

theorem original_norm (v : Fin 28) (x : Coordinates) :
    IntegralBinaryEnergy318.norm (kind v) (coordinates v x 0)
      (coordinates v x 1) (coordinates v x 2) (coordinates v x 3)=integerNorm x := by
  fin_cases v <;>
    norm_num [IntegralBinaryEnergy318.norm,IntegralBinaryEnergy318.binaryNorm,
      kind,coordinates,applyMatrix,inverseMatrix,integerNorm] <;> ring

/-- Exact vertex energy of the literal original quaternion, with every
threshold retained rather than an equivalent-looking quadratic form. -/
theorem original_energy (v : Fin 28) (x : Coordinates) :
    (IntegralBinaryEnergy318.threshold (kind v):ℚ)*denominator (embed x) (vertex v)=
      (IntegralBinaryEnergy318.energy (kind v) (coordinates v x 0)
        (coordinates v x 1) (coordinates v x 2) (coordinates v x 3):ℚ) := by
  rw [denominator_value]
  fin_cases v <;>
    norm_num [IntegralBinaryEnergy318.energy,IntegralBinaryEnergy318.binaryEnergy,
      IntegralBinaryEnergy318.threshold,kind,coordinates,applyMatrix,inverseMatrix,
      embed,vertex] <;> push_cast <;> ring

/-- ALL original integral norm-one quaternions obey every vertex inequality. -/
theorem vertex_minimum (v : Fin 28) (x : Coordinates) (hx : integerNorm x=1) :
    1≤denominator (embed x) (vertex v) := by
  have hn := original_norm v x
  rw [hx] at hn
  have h := IntegralBinaryEnergy318.minimum (kind v) (coordinates v x 0)
    (coordinates v x 1) (coordinates v x 2) (coordinates v x 3) hn
  have hq : (IntegralBinaryEnergy318.threshold (kind v):ℚ)≤
      (IntegralBinaryEnergy318.energy (kind v) (coordinates v x 0)
        (coordinates v x 1) (coordinates v x 2) (coordinates v x 3):ℚ) := by exact_mod_cast h
  rw [← original_energy v x] at hq
  have hp : (0:ℚ)<IntegralBinaryEnergy318.threshold (kind v) := by
    fin_cases v <;> norm_num [IntegralBinaryEnergy318.threshold,kind]
  nlinarith
end PELOriginalVertexEnergy318
