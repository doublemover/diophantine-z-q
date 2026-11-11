module
public import PELActualVertexSectorGerms318
public section
noncomputable section
namespace PELOriginalPolygonBoundary318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318 PELDirichletIncidence318
open PELOriginalDirichletPolygon318 PELOriginalProjectiveTangents318
open PELRealKleinSideTransport318
set_option maxHeartbeats 1800000
@[expose] def signedSide (j : Fin 8) (ε δ : Bool) : Fin 28 :=
  ![(if ε then (if δ then 9 else 9) else (if δ then 8 else 8)),(if ε then (if δ then 25 else 17) else (if δ then 23 else 14)),(if ε then (if δ then 4 else 0) else (if δ then 5 else 1)),(if ε then (if δ then 19 else 18) else (if δ then 12 else 13)),(if ε then (if δ then 7 else 3) else (if δ then 6 else 2)),(if ε then (if δ then 21 else 20) else (if δ then 11 else 10)),(if ε then (if δ then 24 else 16) else (if δ then 22 else 15)),(if ε then (if δ then 27 else 26) else (if δ then 27 else 26))] j
@[expose] def startNeighbor : Fin 28 → Fin 28 := ![17,14,13,18,19,12,11,21,23,25,2,22,6,1,8,10,20,9,0,7,3,24,27,5,27,4,16,24]
@[expose] def finishNeighbor : Fin 28 → Fin 28 := ![18,13,10,20,25,23,12,19,14,17,15,6,5,2,1,26,26,0,3,4,16,7,11,8,21,9,15,22]

@[expose] def realSideValue (e : Fin 28) (P : ℝ × ℝ) : ℝ :=
  (row e 0:ℝ)+(row e 1:ℝ)*P.1+(row e 2:ℝ)*P.2

theorem signed_row_identity (j : Fin 8) (ε δ : Bool) (P : ℝ × ℝ) :
    realSideValue (signedSide j ε δ) P =
      (rowConstant j:ℝ)-(rowFirst j:ℝ)*((sign ε:ℝ)*P.1)-
        (rowSecond j:ℝ)*((sign δ:ℝ)*P.2) := by
  fin_cases j <;> cases ε <;> cases δ <;>
    norm_num [realSideValue,signedSide,row,rowConstant,rowFirst,rowSecond,sign] <;> ring

theorem side_nonnegative (P : ℝ × ℝ) (hP : P ∈ planePolygon) (e : Fin 28) :
    0 ≤ realSideValue e P := by
  have h := hP (selection e).1 (selection e).2.1 (selection e).2.2
  fin_cases e <;>
    norm_num [realSideValue,row,selection,rowFirst,rowSecond,rowConstant,sign] at * <;> linarith

@[expose] def edgeParameter (e : Fin 28) (P : ℝ × ℝ) : ℝ :=
  if (vertex (start e)).1=(vertex (finish e)).1 then
    (P.2-((vertex (start e)).2:ℝ))/(((vertex (finish e)).2:ℝ)-((vertex (start e)).2:ℝ))
  else (P.1-((vertex (start e)).1:ℝ))/(((vertex (finish e)).1:ℝ)-((vertex (start e)).1:ℝ))

/-- The other two literal boundary inequalities give the full closed edge
parameter interval. This covers irrational real points too. -/
theorem edgeParameter_bounds (e : Fin 28) (P : ℝ × ℝ)
    (he : realSideValue e P=0)
    (hs : 0 ≤ realSideValue (startNeighbor e) P)
    (hf : 0 ≤ realSideValue (finishNeighbor e) P) :
    0 ≤ edgeParameter e P ∧ edgeParameter e P ≤ 1 := by
  fin_cases e <;>
    norm_num [realSideValue,row,startNeighbor,finishNeighbor,edgeParameter,
      vertex,start,finish] at * <;> constructor <;> linarith

theorem point_on_edge_line (e : Fin 28) (P : ℝ × ℝ)
    (he : realSideValue e P=0) :
    P=realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) (edgeParameter e P) := by
  fin_cases e <;>
    norm_num [realSideValue,row,edgeParameter,realMix,realPoint,vertex,start,finish] at * <;>
    apply Prod.ext <;> change _ = _ <;> norm_num <;> linarith

theorem whole_boundary_side (e : Fin 28) (P : ℝ × ℝ)
    (hP : P∈planePolygon) (he : realSideValue e P=0) :
    ∃ s : ℝ, 0≤s ∧ s≤1 ∧
      P=realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s := by
  have hb := edgeParameter_bounds e P he (side_nonnegative P hP _) (side_nonnegative P hP _)
  exact ⟨edgeParameter e P,hb.1,hb.2,point_on_edge_line e P he⟩
end PELOriginalPolygonBoundary318
