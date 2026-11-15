module
public import PELNormalizerOctagonStrict318
public import PELPositiveNormalizerKlein318
public section
namespace PELNormalizerOctagonRealImages318
open PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318 PELQuaternionKleinAction318
open PELNormalizerOctagonVertices318 PELNormalizerOctagonEquality318
open PELNormalizerOctagonImageCertificate318 PELNormalizerOctagonStrata318
open PELNormalizerOctagonMinimum318 NormalizerVertexEnergyMinimum318
open PELPositiveNormalizerKlein318
set_option maxHeartbeats 5000000
@[expose] def signR (b : Bool) (z : ℝ) : ℝ := if b then z else -z

theorem cast_rows (x : Coordinates) (P : Point) (a b : Bool)
    (h : matrix (embed x) *ᵥ vector P=(integerNorm x:ℚ) • signedVector a b P) :
    realRow (embed x) 0 P.1 P.2=(integerNorm x:ℝ)*signR a P.1 ∧
    realRow (embed x) 1 P.1 P.2=(integerNorm x:ℝ)*signR b P.2 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  cases a <;> cases b <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,vector,signedVector,signR,realRow] at h0 h1 ⊢ <;>
    constructor <;> first | exact_mod_cast h0 | exact_mod_cast h1

theorem row_mix (x : Coordinates) (k : Fin 3) (v : Fin 8) (s : ℝ) :
    realRow (embed x) k (mix v s).1 (mix v s).2=
      (1-s)*realRow (embed x) k (vertex v).1 (vertex v).2+
        s*realRow (embed x) k (vertex (next v)).1 (vertex (next v)).2 := by
  unfold realRow mix
  ring

theorem integer_vertex_rows (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ)) (v : Fin 8)
    (he : realDen (embed x) (vertex v).1 (vertex v).2=(allowedNorm i:ℝ)) :
    ∃ a b : Bool,
      realRow (embed x) 0 (vertex v).1 (vertex v).2=(allowedNorm i:ℝ)*signR a (vertex v).1 ∧
      realRow (embed x) 1 (vertex v).1 (vertex v).2=(allowedNorm i:ℝ)*signR b (vertex v).2 := by
  have heQ : denominator (embed x) (vertex v)=(allowedNorm i:ℚ) := by
    rw [realDen_cast] at he
    exact_mod_cast he
  obtain ⟨j,hj⟩ := integer_vertex_equality i x hn v heQ
  obtain ⟨a,b,hab⟩ := vertex_images v j
  rw [←hj] at hab
  have h := cast_rows x (vertex v) a b hab
  rw [hn] at h
  exact ⟨a,b,h⟩

/-- Whole real open sides, not rational samples: affine equality forces
both endpoint equalities, and a common exact sign pair then controls all
three homogeneous rows at the original real point. -/
theorem integer_open_side_rows (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ)) (v : Fin 8) (s : ℝ) (hs : 0<s) (hs1 : s<1)
    (he : realDen (embed x) (mix v s).1 (mix v s).2=(allowedNorm i:ℝ)) :
    ∃ a b : Bool,
      realRow (embed x) 0 (mix v s).1 (mix v s).2=(allowedNorm i:ℝ)*signR a (mix v s).1 ∧
      realRow (embed x) 1 (mix v s).1 (mix v s).2=(allowedNorm i:ℝ)*signR b (mix v s).2 := by
  have h0 : (allowedNorm i:ℝ)≤realDen (embed x) (vertex v).1 (vertex v).2 := by
    rw [realDen_cast]; exact_mod_cast all_vertex_minimum i x hn v
  have h1 : (allowedNorm i:ℝ)≤realDen (embed x) (vertex (next v)).1 (vertex (next v)).2 := by
    rw [realDen_cast]; exact_mod_cast all_vertex_minimum i x hn (next v)
  have hm := row_mix x 2 v s
  change realDen (embed x) (mix v s).1 (mix v s).2=
    (1-s)*realDen (embed x) (vertex v).1 (vertex v).2+
      s*realDen (embed x) (vertex (next v)).1 (vertex (next v)).2 at hm
  have he0 : realDen (embed x) (vertex v).1 (vertex v).2=(allowedNorm i:ℝ) := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h1)]
  have he1 : realDen (embed x) (vertex (next v)).1 (vertex (next v)).2=(allowedNorm i:ℝ) := by
    nlinarith [mul_nonneg (by linarith : 0≤1-s) (sub_nonneg.mpr h0)]
  rw [realDen_cast] at he0 he1
  have hq0 : denominator (embed x) (vertex v)=(allowedNorm i:ℚ) := by exact_mod_cast he0
  have hq1 : denominator (embed x) (vertex (next v))=(allowedNorm i:ℚ) := by exact_mod_cast he1
  obtain ⟨j,hj⟩ := integer_vertex_equality i x hn v hq0
  have hsecond : denominator (embed (vertexRow v j)) (vertex (next v))=
      (integerNorm (vertexRow v j):ℚ) := by rw [←hj,hn]; exact hq1
  obtain ⟨a,b,ha,hb⟩ := edge_images v j hsecond
  rw [←hj] at ha hb
  have hstart := cast_rows x (vertex v) a b ha
  have hend := cast_rows x (vertex (next v)) a b hb
  rw [hn] at hstart hend
  refine ⟨a,b,?_,?_⟩
  · rw [row_mix,hstart.1,hend.1]
    cases a <;> simp [signR,mix] <;> ring
  · rw [row_mix,hstart.2,hend.2]
    cases b <;> simp [signR,mix] <;> ring
end PELNormalizerOctagonRealImages318
