module
public import IntegralBinaryEnergyMinimizers318
public import PELOriginalVertexEnergy318
public import PELDirichletVertexCycles318
public section
noncomputable section
namespace PELOriginalVertexEquality318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318
open PELQuaternionKleinAction318 PELOriginalVertexEnergy318
open IntegralBinaryEnergyMinimizers318
set_option maxHeartbeats 3000000

@[expose] def equalityCoordinates (v : Fin 28) (k : Fin 16) : Coordinates :=
  applyMatrix (forwardMatrix v) (minimizer (kind v) k)

/-- Every original unit whose multiplier is1 at the literal vertex occurs
in the exact finite equality list. No bound on its original coordinates is
assumed: the unimodular reduced-energy proof constructs the bound. -/
theorem complete_equality_list (v : Fin 28) (x : Coordinates)
    (hn : integerNorm x=1) (he : denominator (embed x) (vertex v)=1) :
    ∃ k : Fin 16, x=equalityCoordinates v k := by
  have hn' := original_norm v x
  rw [hn] at hn'
  have he' := original_energy v x
  rw [he,mul_one] at he'
  have hi : IntegralBinaryEnergy318.energy (kind v) (coordinates v x 0)
      (coordinates v x 1) (coordinates v x 2) (coordinates v x 3)=
      IntegralBinaryEnergy318.threshold (kind v) := by exact_mod_cast he'.symm
  obtain ⟨k,hk⟩ := IntegralBinaryEnergyMinimizers318.equality (kind v)
    (coordinates v x 0) (coordinates v x 1) (coordinates v x 2) (coordinates v x 3) hn' hi
  have hc : coordinates v x=minimizer (kind v) k := by
    have hx : coordinates v x=![coordinates v x 0,coordinates v x 1,
        coordinates v x 2,coordinates v x 3] := by
      ext i; fin_cases i <;> rfl
    exact hx.trans hk
  refine ⟨k,?_⟩
  exact (inverse_forward v x).2.symm.trans
    (congrArg (applyMatrix (forwardMatrix v)) hc)

@[expose] def imageVertex : Fin 28 → Fin 16 → Fin 28 := ![![26,12,13,27,14,15,0,1,1,0,15,14,27,13,12,26],![26,12,13,27,14,15,0,1,1,0,15,14,27,13,12,26],![25,11,10,24,17,3,2,16,16,2,3,17,24,10,11,25],![25,11,10,24,17,3,2,16,16,2,3,17,24,10,11,25],![22,23,4,5,5,4,23,22,22,23,4,5,5,4,23,22],![22,23,4,5,5,4,23,22,22,23,4,5,5,4,23,22],![20,6,7,21,21,7,6,20,20,6,7,21,21,7,6,20],![7,21,20,6,6,20,21,7,7,21,20,6,6,20,21,7],![18,19,8,9,9,8,19,18,18,19,8,9,9,8,19,18],![18,19,8,9,9,8,19,18,18,19,8,9,9,8,19,18],![25,11,10,24,17,3,2,16,16,2,3,17,24,10,11,25],![25,11,10,24,17,3,2,16,16,2,3,17,24,10,11,25],![12,26,27,13,0,1,14,15,15,14,1,0,13,27,26,12],![15,1,0,14,27,26,13,12,12,13,26,27,14,0,1,15],![13,27,26,12,1,0,15,14,14,15,0,1,12,26,27,13],![14,0,1,15,26,27,12,13,13,12,27,26,15,1,0,14],![24,10,11,25,16,2,3,17,17,3,2,16,25,11,10,24],![24,10,11,25,16,2,3,17,17,3,2,16,25,11,10,24],![18,19,8,9,9,8,19,18,18,19,8,9,9,8,19,18],![18,19,8,9,9,8,19,18,18,19,8,9,9,8,19,18],![21,7,6,20,20,6,7,21,21,7,6,20,20,6,7,21],![6,20,21,7,7,21,20,6,6,20,21,7,7,21,20,6],![22,23,4,5,5,4,23,22,22,23,4,5,5,4,23,22],![22,23,4,5,5,4,23,22,22,23,4,5,5,4,23,22],![24,10,11,25,16,2,3,17,17,3,2,16,25,11,10,24],![24,10,11,25,16,2,3,17,17,3,2,16,25,11,10,24],![27,13,12,26,15,14,1,0,0,1,14,15,26,12,13,27],![27,13,12,26,15,14,1,0,0,1,14,15,26,12,13,27]]

/-- The finite table acts through the ORIGINAL quaternion representation. -/
theorem literal_vertex_image (v : Fin 28) (k : Fin 16) :
    action (embed (equalityCoordinates v k)) (vertex v)=vertex (imageVertex v k) := by
  fin_cases v <;> fin_cases k <;>
    norm_num [action,denominator,matrix,vector,equalityCoordinates,applyMatrix,
      forwardMatrix,kind,minimizer,embed,vertex,imageVertex,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem image_same_class (v : Fin 28) (k : Fin 16) :
    PELDirichletVertexCycles318.vertexClass (imageVertex v k)=
      PELDirichletVertexCycles318.vertexClass v := by
  fin_cases v <;> fin_cases k <;> rfl

/-- Every equality unit takes the vertex to one in the SAME original
endpoint-graph class. This is exhaustion, not selected unit examples. -/
theorem every_vertex_equality (v : Fin 28) (x : Coordinates)
    (hn : integerNorm x=1) (he : denominator (embed x) (vertex v)=1) :
    ∃ w : Fin 28, PELDirichletVertexCycles318.vertexClass w=
      PELDirichletVertexCycles318.vertexClass v ∧ action (embed x) (vertex v)=vertex w := by
  obtain ⟨k,rfl⟩ := complete_equality_list v x hn he
  exact ⟨imageVertex v k,image_same_class v k,literal_vertex_image v k⟩
end PELOriginalVertexEquality318
