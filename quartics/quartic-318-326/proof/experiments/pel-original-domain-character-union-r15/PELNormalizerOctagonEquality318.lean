module
public import NormalizerVertexEnergyEquality318
public section
namespace PELNormalizerOctagonEquality318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELQuaternionKleinAction318 PELNormalizerOctagonVertices318
open NormalizerVertexEnergyMinimum318 NormalizerVertexEnergyEquality318
set_option maxHeartbeats 5000000

@[expose] def unsignedCoordinates (k : Fin 2) (j : Fin 16) (a b : Bool) : Coordinates :=
  let w := equalityRow k j
  let c := sign b (w 2)
  let d := sign a (w 3)
  let r := sign a (sign b (w 1))
  ![(w 0-c)/2,(r-d)/2,c,d]

@[expose] def vertexRow (v : Fin 8) (j : Fin 16) : Coordinates :=
  unsignedCoordinates (vertexChoice v).1 j (vertexChoice v).2.1 (vertexChoice v).2.2

theorem recover_coordinates (x : Coordinates) (k : Fin 2) (j : Fin 16) (a b : Bool)
    (h : equalityRow k j=![sCoord x,sign a (sign b (rCoord x)),sign b (x 2),sign a (x 3)]) :
    x=unsignedCoordinates k j a b := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  cases a <;> cases b <;>
    simp [sign,sCoord,rCoord] at h0 h1 h2 h3 <;>
    ext n <;> fin_cases n <;> simp [unsignedCoordinates,sign] <;> omega

/-- Exact classification at an arbitrary signed vertex, for every integer
original coordinate vector of every possible primitive normalizer norm. -/
theorem integer_vertex_equality (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ)) (v : Fin 8)
    (he : denominator (embed x) (vertex v)=(allowedNorm i:ℚ)) :
    ∃ j : Fin 16,x=vertexRow v j := by
  let k := (vertexChoice v).1
  let a := (vertexChoice v).2.1
  let b := (vertexChoice v).2.2
  have hnorm := signed_norm x a b
  rw [hn] at hnorm
  have hden : denominator (embed x) (signedPoint k a b)=(allowedNorm i:ℚ) := by
    simpa only [vertex_choice,k,a,b] using he
  have henergy : energy k (sCoord x) (sign a (sign b (rCoord x)))
      (sign b (x 2)) (sign a (x 3))=threshold k (allowedNorm i) := by
    have hr := energy_denominator k x a b
    rw [hden] at hr
    fin_cases k <;> norm_num [coefficient,threshold] at hr ⊢ <;> exact_mod_cast hr
  obtain ⟨j,hj⟩ := whole_integer_equality i k _ _ _ _ hnorm henergy
  exact ⟨j,recover_coordinates x k j a b hj⟩
end PELNormalizerOctagonEquality318
