module
public import PELOriginalVertexEquality318
public import PELOriginalInteriorUniqueness318
public section
noncomputable section
namespace PELOriginalEdgeEquality318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318
open PELQuaternionKleinAction318 PELOriginalVertexEnergy318
open IntegralBinaryEnergyMinimizers318 PELOriginalVertexEquality318
set_option maxHeartbeats 3000000

/-- The intersection of the complete equality sets at the two endpoints
contains precisely the central signs and the two signs of the ORIGINAL
side-pairing unit. No arbitrary unit-generation hypothesis is used. -/
theorem endpoint_equalities (e : Fin 28) (x : Coordinates)
    (hn : integerNorm x=1)
    (hs : denominator (embed x) (vertex (start e))=1)
    (hf : denominator (embed x) (vertex (finish e))=1) :
    x = ![1,0,0,0] ∨ x = ![-1,0,0,0] ∨ x=coefficients e ∨ x= -coefficients e := by
  obtain ⟨k,rfl⟩ := complete_equality_list (start e) x hn hs
  fin_cases e <;> fin_cases k <;>
    norm_num [denominator,matrix,vector,equalityCoordinates,applyMatrix,
      forwardMatrix,kind,minimizer,embed,vertex,start,finish,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three] at hf ⊢ <;>
    norm_num [coefficients] <;> decide

/-- An interior point of the WHOLE real side can have multiplier1 only
when both endpoint multipliers are1. The strict parameter inequalities are
necessary; the endpoints use the separate vertex classification. -/
theorem real_edge_endpoint_equalities (M : PELRealProjectiveDifferential318.HomogeneousMatrix)
    (e : Fin 28) (s : ℝ) (hs : 0<s) (hs1 : s<1)
    (hstart : 1≤PELRealProjectiveDifferential318.denominator M
      (PELOriginalProjectiveTangents318.realPoint (vertex (start e))))
    (hfinish : 1≤PELRealProjectiveDifferential318.denominator M
      (PELOriginalProjectiveTangents318.realPoint (vertex (finish e))))
    (he : PELRealProjectiveDifferential318.denominator M
      (PELRealKleinSideTransport318.realMix
        (PELOriginalProjectiveTangents318.realPoint (vertex (start e)))
        (PELOriginalProjectiveTangents318.realPoint (vertex (finish e))) s)=1) :
    PELRealProjectiveDifferential318.denominator M
      (PELOriginalProjectiveTangents318.realPoint (vertex (start e)))=1 ∧
    PELRealProjectiveDifferential318.denominator M
      (PELOriginalProjectiveTangents318.realPoint (vertex (finish e)))=1 := by
  rw [PELRealKleinSideTransport318.denominator_mix] at he
  constructor <;> nlinarith
/-- Complete equality classification on every OPEN real original side.
This retains the same embedded integral order element throughout. -/
theorem every_real_edge_equality (e : Fin 28) (x : Coordinates)
    (hn : integerNorm x=1) (s : ℝ) (hs : 0<s) (hs1 : s<1)
    (he : PELRealProjectiveDifferential318.denominator
      (PELOriginalProjectiveTangents318.realMatrix (embed x))
      (PELRealKleinSideTransport318.realMix
        (PELOriginalProjectiveTangents318.realPoint (vertex (start e)))
        (PELOriginalProjectiveTangents318.realPoint (vertex (finish e))) s)=1) :
    x = ![1,0,0,0] ∨ x = ![-1,0,0,0] ∨ x=coefficients e ∨ x= -coefficients e := by
  have hstart : 1≤PELRealProjectiveDifferential318.denominator
      (PELOriginalProjectiveTangents318.realMatrix (embed x))
      (PELOriginalProjectiveTangents318.realPoint (vertex (start e))) := by
    rw [PELOriginalProjectiveTangents318.denominator_cast]
    exact_mod_cast PELOriginalVertexEnergy318.vertex_minimum (start e) x hn
  have hfinish : 1≤PELRealProjectiveDifferential318.denominator
      (PELOriginalProjectiveTangents318.realMatrix (embed x))
      (PELOriginalProjectiveTangents318.realPoint (vertex (finish e))) := by
    rw [PELOriginalProjectiveTangents318.denominator_cast]
    exact_mod_cast PELOriginalVertexEnergy318.vertex_minimum (finish e) x hn
  obtain ⟨hA,hB⟩ := real_edge_endpoint_equalities _ e s hs hs1 hstart hfinish he
  rw [PELOriginalProjectiveTangents318.denominator_cast] at hA hB
  exact endpoint_equalities e x hn (by exact_mod_cast hA) (by exact_mod_cast hB)
end PELOriginalEdgeEquality318
