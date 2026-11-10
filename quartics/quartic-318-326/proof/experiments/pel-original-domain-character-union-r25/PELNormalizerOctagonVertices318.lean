module
public import NormalizerVertexEnergyMinimum318
public import PELDirichletSidePairingData318
public section
namespace PELNormalizerOctagonVertices318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELDirichletOriginalUnits318 PELQuaternionKleinAction318
open NormalizerVertexEnergyBounds318 NormalizerVertexEnergyMinimum318
set_option maxHeartbeats 3000000

@[expose] def sCoord (x : Coordinates) : ℤ := 2*x 0+x 2
@[expose] def rCoord (x : Coordinates) : ℤ := 2*x 1+x 3
@[expose] def first (k : Fin 2) : ℚ := if k=0 then 28 else 30
@[expose] def second (k : Fin 2) : ℚ := if k=0 then 1 else 5/7
@[expose] def coefficient (k : Fin 2) : ℚ := if k=0 then 20 else 28
@[expose] def signedPoint (k : Fin 2) (a b : Bool) : Point :=
  ((if a then 1 else -1)*first k,(if b then 1 else -1)*second k)

/-- This norm relation uses the original integral basis; no denominator
or quaternion polarization is rescaled. -/
theorem norm_relation (x : Coordinates) :
    (sCoord x)^2+210*(rCoord x)^2-5*(x 2)^2-42*(x 3)^2=4*integerNorm x := by
  unfold sCoord rCoord integerNorm
  ring

/-- Changing the two geometric coordinate signs is an exact sign change
of the four integer search coordinates; the norm stays unchanged. -/
theorem signed_norm (x : Coordinates) (a b : Bool) :
    (sCoord x)^2+210*(sign a (sign b (rCoord x)))^2-
      5*(sign b (x 2))^2-42*(sign a (x 3))^2=4*integerNorm x := by
  cases a <;> cases b <;> simpa only [sign,ite_true,ite_false,neg_sq] using norm_relation x

/-- Exact energy normalization against the ACTUAL rational quaternion
height multiplier at every one of the eight signed octagon vertices. -/
theorem energy_denominator (k : Fin 2) (x : Coordinates) (a b : Bool) :
    (energy k (sCoord x) (sign a (sign b (rCoord x)))
      (sign b (x 2)) (sign a (x 3)):ℚ)=
        coefficient k*denominator (embed x) (signedPoint k a b) := by
  fin_cases k <;> cases a <;> cases b <;>
    norm_num [energy,energy0,energy1,sign,sCoord,rCoord,coefficient,signedPoint,first,second,
      denominator_value,embed] <;> push_cast <;> ring

/-- All integer original order vectors of each allowed positive norm
satisfy the actual normalizer inequality at EVERY signed vertex. -/
theorem signed_vertex_minimum (i : Fin 16) (x : Coordinates)
    (hx : integerNorm x=(allowedNorm i:ℤ)) (k : Fin 2) (a b : Bool) :
    (allowedNorm i:ℚ)≤denominator (embed x) (signedPoint k a b) := by
  have hn := signed_norm x a b
  rw [hx] at hn
  have he := whole_integer_minimum i k (sCoord x) (sign a (sign b (rCoord x)))
    (sign b (x 2)) (sign a (x 3)) hn
  have heQ : (threshold k (allowedNorm i):ℚ)≤
      (energy k (sCoord x) (sign a (sign b (rCoord x)))
        (sign b (x 2)) (sign a (x 3)):ℚ) := by exact_mod_cast he
  rw [energy_denominator] at heQ
  fin_cases k <;> norm_num [threshold,coefficient] at heQ <;> linarith

@[expose] def vertex : Fin 8 → Point := ![
  (28,1),(-28,1),(-30,5/7),(-30,-5/7),(-28,-1),(28,-1),(30,-5/7),(30,5/7)]
@[expose] def vertexChoice : Fin 8 → Fin 2 × Bool × Bool := ![
  (0,true,true),(0,false,true),(1,false,true),(1,false,false),
  (0,false,false),(0,true,false),(1,true,false),(1,true,true)]
theorem vertex_choice (v : Fin 8) : vertex v=
    signedPoint (vertexChoice v).1 (vertexChoice v).2.1 (vertexChoice v).2.2 := by
  fin_cases v <;> norm_num [vertex,vertexChoice,signedPoint,first,second]

theorem all_vertex_minimum (i : Fin 16) (x : Coordinates)
    (hx : integerNorm x=(allowedNorm i:ℤ)) (v : Fin 8) :
    (allowedNorm i:ℚ)≤denominator (embed x) (vertex v) := by
  rw [vertex_choice]
  exact signed_vertex_minimum i x hx _ _ _
end PELNormalizerOctagonVertices318
