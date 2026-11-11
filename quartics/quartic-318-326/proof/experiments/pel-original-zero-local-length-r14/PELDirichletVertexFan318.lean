module
public import PELDirichletVertexCycles318
public section
noncomputable section
namespace PELDirichletVertexFan318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELQuaternionKleinAction318 PELDirichletSidePairingData318 PELDirichletVertexCycles318
open PELDirichletOriginalUnits318
open scoped BigOperators
set_option maxHeartbeats 1800000

/-- Exact original accumulated word taking the cycle's first vertex to v. -/
@[expose] def prefixWord : Fin 28 → List (Fin 28) := ![[],[24,9,23],[],[21,16,0,14,10],[],[7],[],[7],[],[4],[21,16,0,14,10,22,5],[21,16,0,14,10,22],[24],[24,9],[24,9,23,27,15,8],[24,9,23,27,15],[21,16],[21,16,0],[4,12,1],[4,12],[7,12,2],[7,12],[7,11,2],[7,11],[21],[21,16,0,14],[24,9,23,27,15,8,17],[24,9,23,27]]
@[expose] def prefixCoordinates : Fin 28 → Coordinates := ![![1,0,0,0],![-13,2,0,-6],![1,0,0,0],![43,-6,0,16],![1,0,0,0],![29,-4,0,10],![1,0,0,0],![29,-4,0,10],![1,0,0,0],![43,-6,0,14],![-1,0,6,-1],![-41,6,-6,-15],![1,0,-6,1],![13,-2,6,5],![1,0,7,-1],![-13,2,-7,-5],![1,1,-21,1],![43,-7,21,15],![-1,-1,14,0],![-41,7,-14,-14],![-1,-1,14,0],![29,-5,14,10],![1,-1,15,0],![-29,5,-15,-10],![1,-1,15,0],![-41,7,-27,-14],![-1,0,-1,0],![13,-2,13,4]]
@[expose] def otherVertex : Fin 28 → Fin 28 := ![2,0,4,1,6,3,4,9,10,7,12,9,14,11,16,13,18,15,20,17,18,23,24,21,26,23,27,25]
@[expose] def ray : Fin 28 → Point := ![(-165,13),(-1,0),(-17,2),(675,-73),(-210,29),(-17,2),(210,-29),(6,-1),(-210,43),(-6,1),(165,-13),(420,-43),(-210,13),(-255,13),(255,-13),(210,-13),(-420,43),(-165,13),(6,-1),(210,-43),(-6,1),(-210,29),(17,-2),(210,-29),(-675,73),(17,-2),(1,0),(165,-13)]
@[expose] def rayScale : Fin 28 → ℚ := ![(140/4251),(560/13),(840/7957),(140/4251),(5/2628),(840/7957),(5/2628),(35/144),(5/5232),(35/144),(140/4251),(5/5232),(10/507),(140/4251),(140/4251),(10/507),(5/5232),(140/4251),(35/144),(5/5232),(35/144),(5/2628),(840/7957),(5/2628),(140/4251),(840/7957),(560/13),(140/4251)]
@[expose] def orientation : Fin 5 → ℤ := ![1,1,1,-1,1]

theorem prefix_original (v : Fin 28) :
    embed (prefixCoordinates v)=originalWord (prefixWord v) := by
  rw [←word_identity]
  congr 1
  fin_cases v <;> ext k <;> fin_cases k <;>
    norm_num [prefixCoordinates,prefixWord,wordCoordinates,product,coefficients]

theorem other_endpoint (v : Fin 28) :
    ({v,otherVertex v}:Finset (Fin 28))={start (stepEdge v),finish (stepEdge v)} := by
  fin_cases v <;> decide

/-- Exact rational quotient-rule expression for the projective tangent map.
The analytic differentiability/real-coordinate comparison is not asserted here. -/
@[expose] def tangentFormula (q : B) (P W : Point) : Point :=
  let M := matrix q
  let d := denominator q P
  let l := M 2 0*W.1+M 2 1*W.2
  (((M 0 0*W.1+M 0 1*W.2)*d-(M*ᵥvector P) 0*l)/d^2,
   ((M 1 0*W.1+M 1 1*W.2)*d-(M*ᵥvector P) 1*l)/d^2)

@[expose] def sideDirection (v : Fin 28) : Point :=
  ((vertex (otherVertex v)).1-(vertex v).1,(vertex (otherVertex v)).2-(vertex v).2)

/-- Each pulled-back side tangent is the listed primitive ray with a
strictly POSITIVE factor. Both the original accumulated quaternion and the
original side direction occur in the displayed formula. -/
theorem original_tangent_ray (v : Fin 28) :
    tangentFormula (embed (conjugateCoordinates (prefixCoordinates v)))
      (vertex v) (sideDirection v)=
      (rayScale v*(ray v).1,rayScale v*(ray v).2) := by
  fin_cases v <;>
    norm_num [tangentFormula,denominator,matrix,vector,conjugateCoordinates,
      prefixCoordinates,embed,vertex,sideDirection,otherVertex,rayScale,ray,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem scale_positive (v : Fin 28) : 0<rayScale v := by
  fin_cases v <;> norm_num [rayScale]

theorem inverse_denominator_positive (v : Fin 28) :
    0<denominator (embed (conjugateCoordinates (prefixCoordinates v))) (vertex v) := by
  fin_cases v <;> norm_num [denominator,matrix,vector,conjugateCoordinates,
    prefixCoordinates,embed,vertex,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

@[expose] def cross (P Q : Point) : ℚ := P.1*Q.2-P.2*Q.1

theorem oriented_cross_positive (v : Fin 28) :
    0<(orientation (vertexClass v):ℚ)*cross (ray v) (ray (nextVertex v)) := by
  fin_cases v <;> norm_num [orientation,vertexClass,cross,ray,nextVertex]

/-- Signed crossings of the positive horizontal axis, as a literal finite
arithmetic certificate. Its interpretation as a topological winding number
belongs to the polygon-local-chart theorem. -/
@[expose] def axisCrossing (P Q : Point) : ℤ :=
  if P.2≤0 ∧ 0<Q.2 ∧ 0<cross P Q then 1
  else if Q.2≤0 ∧ 0<P.2 ∧ cross P Q<0 then -1 else 0

theorem one_signed_axis_turn (i : Fin 5) :
    ∑ v : Fin 28, (if vertexClass v=i then axisCrossing (ray v) (ray (nextVertex v)) else 0)
      =orientation i := by
  fin_cases i <;> norm_num [vertexClass,axisCrossing,ray,nextVertex,cross,orientation,
    Fin.sum_univ_succ]
end PELDirichletVertexFan318
