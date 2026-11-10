module
public import PELNormalizerOctagonEquality318
public section
namespace PELNormalizerOctagonImageCertificate318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELQuaternionKleinAction318 PELNormalizerOctagonVertices318 PELNormalizerOctagonEquality318
open NormalizerVertexEnergyMinimum318 NormalizerVertexEnergyEquality318
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
@[expose] def next (v : Fin 8) : Fin 8 := ⟨(v.val+1)%8,Nat.mod_lt _ (by decide)⟩
@[expose] def signedVector (a b : Bool) (P : Point) : Fin 3 → ℚ :=
  ![if a then P.1 else -P.1,if b then P.2 else -P.2,1]

/-- Every equality vector at a vertex sends it to an independent sign
change of that SAME literal vertex; no different vertex magnitude appears. -/
theorem vertex_images (v : Fin 8) (j : Fin 16) :
    ∃ a b : Bool,matrix (embed (vertexRow v j)) *ᵥ vector (vertex v)=
      (integerNorm (vertexRow v j):ℚ) • signedVector a b (vertex v) := by
  revert v j
  decide

/-- Equality at both endpoints permits the SAME sign pair at both
endpoints. Affinity therefore controls the entire real side, not just its
finite endpoints. The second endpoint equality is retained explicitly. -/
theorem edge_images (v : Fin 8) (j : Fin 16)
    (h : denominator (embed (vertexRow v j)) (vertex (next v))=
      (integerNorm (vertexRow v j):ℚ)) :
    ∃ a b : Bool,
      matrix (embed (vertexRow v j)) *ᵥ vector (vertex v)=
        (integerNorm (vertexRow v j):ℚ) • signedVector a b (vertex v) ∧
      matrix (embed (vertexRow v j)) *ᵥ vector (vertex (next v))=
        (integerNorm (vertexRow v j):ℚ) • signedVector a b (vertex (next v)) := by
  revert h
  fin_cases v <;> fin_cases j <;> decide

/-- The simultaneous-sign alternatives are the ONLY equality vectors
valid at every vertex, including the center-isotropy vector of norm210. -/
theorem all_vertex_coordinates (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ))
    (he : ∀ v : Fin 8,denominator (embed x) (vertex v)=(allowedNorm i:ℚ)) :
    x=![1,0,0,0] ∨ x=![-1,0,0,0] ∨ x=![0,1,0,0] ∨ x=![0,-1,0,0] := by
  obtain ⟨j,hj⟩ := integer_vertex_equality i x hn 0 (he 0)
  subst x
  have hh : ∀ v : Fin 8,denominator (embed (vertexRow 0 j)) (vertex v)=
      (integerNorm (vertexRow 0 j):ℚ) := by simpa only [hn] using he
  have h4 := hh 4
  fin_cases j <;>
    norm_num [vertexRow,unsignedCoordinates,vertexChoice,equalityRow,NormalizerVertexEnergyMinimum318.sign,
      integerNorm,vertex,denominator_value,embed] at h4 ⊢
end PELNormalizerOctagonImageCertificate318
