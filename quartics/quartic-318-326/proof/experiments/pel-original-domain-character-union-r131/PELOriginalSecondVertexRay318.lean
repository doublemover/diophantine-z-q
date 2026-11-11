module
public import PELOriginalLocalCones318
public import PELOriginalRealFanCover318
public section
noncomputable section
namespace PELOriginalSecondVertexRay318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionKleinAction318
open PELDirichletSidePairingData318 PELDirichletVertexCycles318 PELDirichletVertexFan318
open PELOriginalProjectiveTangents318 PELOriginalVertexDerivatives318
open PELDirichletOriginalUnits318 PELOriginalLocalCones318 PELOriginalRealFanCover318
set_option maxHeartbeats 1800000
@[expose] def previousVertex : Fin 28 → Fin 28 := ![26,13,10,25,22,4,20,6,18,8,11,3,0,12,15,27,24,16,19,9,21,7,23,5,2,17,14,1]
@[expose] def secondEndpoint : Fin 28 → Fin 28 := ![1,3,0,5,2,7,8,5,6,11,8,13,10,15,12,17,14,19,16,21,22,19,20,25,22,27,24,26]
@[expose] def secondRayScale : Fin 28 → ℚ := ![560/13,140/4251,140/4251,840/7957,840/7957,5/2628,35/144,5/2628,35/144,5/5232,5/5232,140/4251,140/4251,10/507,10/507,140/4251,140/4251,5/5232,5/5232,35/144,5/2628,35/144,5/2628,840/7957,840/7957,140/4251,140/4251,560/13]

@[expose] def secondDirection (v : Fin 28) : Point :=
  ((vertex (secondEndpoint v)).1-(vertex v).1,
   (vertex (secondEndpoint v)).2-(vertex v).2)

theorem previous_next (v : Fin 28) : nextVertex (previousVertex v)=v := by
  fin_cases v <;> rfl

theorem previous_class (v : Fin 28) : vertexClass (previousVertex v)=vertexClass v := by
  fin_cases v <;> rfl

theorem secondScale_positive (v : Fin 28) : 0<secondRayScale v := by
  fin_cases v <;> norm_num [secondRayScale]

/-- The OTHER actual incident edge maps to the PREVIOUS cycle ray.
This indexing cannot be replaced with nextVertex. -/
theorem original_second_tangent (v : Fin 28) :
    tangentFormula (inversePrefix v) (vertex v) (secondDirection v)=
      (secondRayScale v*(ray (previousVertex v)).1,
       secondRayScale v*(ray (previousVertex v)).2) := by
  fin_cases v <;>
    norm_num [tangentFormula,inversePrefix,denominator,matrix,vector,conjugateCoordinates,
      prefixCoordinates,embed,vertex,secondDirection,secondEndpoint,secondRayScale,
      previousVertex,ray,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem actual_second_tangent (v : Fin 28) :
    PELRealProjectiveDifferential318.differential
      (realMatrix (inversePrefix v)) (realPoint (vertex v)) (realPoint (secondDirection v))=
      (secondRayScale v:ℝ) • realPoint (ray (previousVertex v)) := by
  rw [differential_cast _ _ _ (inverse_denominator_positive v).ne']
  rw [original_second_tangent]
  apply Prod.ext <;> simp [realPoint]

/-- Both literal incident edges determine the FULL original active cone;
all original signed rows remain in the left side. -/
theorem original_cone_cross_iff (v : Fin 28) (W : ℝ × ℝ) :
    W ∈ vertexCone v ↔
      0 ≤ (orientation (vertexClass v):ℝ)*realCross (realPoint (secondDirection v)) W ∧
      0 ≤ (orientation (vertexClass v):ℝ)*realCross W (realPoint (sideDirection v)) := by
  change (∀ (i : Fin 8 × Bool × Bool),
    linearRow i (realPoint (vertex v))=constantRow i → linearRow i W≤0) ↔ _
  simp only [Prod.forall]
  fin_cases v <;>
    norm_num [linearRow,constantRow,realPoint,vertex,secondDirection,secondEndpoint,
      sideDirection,otherVertex,realCross,orientation,vertexClass,rowFirst,rowSecond,
      rowConstant,sign,Fin.forall_fin_succ,Bool.forall_bool] <;>
    constructor <;> intro h <;> rcases h with ⟨h1,h2⟩ <;> constructor <;> linarith
end PELOriginalSecondVertexRay318
