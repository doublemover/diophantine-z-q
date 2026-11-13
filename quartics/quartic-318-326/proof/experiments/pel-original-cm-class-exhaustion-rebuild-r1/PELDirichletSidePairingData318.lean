module
public import PELQuaternionKleinAction318
public import PELDirichletOriginalUnits318
public section
noncomputable section
namespace PELDirichletSidePairingData318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELQuaternionKleinAction318 PELDirichletOriginalUnits318 PELJointNormOneAction318
set_option maxHeartbeats 1800000

/-- The exact28 original order elements used by the independent polygon
calculation. Every listed element is an ACTUAL norm-one order unit. -/
@[expose] def coefficients : Fin 28 → Coordinates := ![
  ![43,-8,0,14],
  ![-43,-8,0,14],
  ![-29,-6,0,10],
  ![29,-6,0,10],
  ![43,-6,0,14],
  ![-43,-6,0,14],
  ![-29,-4,0,10],
  ![29,-4,0,10],
  ![-13,-2,0,4],
  ![13,-2,0,4],
  ![16,-1,-15,0],
  ![-1,-1,-15,0],
  ![1,-1,-14,0],
  ![13,-1,-14,0],
  ![1,-1,-6,1],
  ![5,-1,-6,1],
  ![-5,-1,6,1],
  ![-1,-1,6,1],
  ![-13,-1,14,0],
  ![-1,-1,14,0],
  ![-16,-1,15,0],
  ![1,-1,15,0],
  ![1,0,-6,-1],
  ![5,0,-6,-1],
  ![1,0,-6,1],
  ![5,0,-6,1],
  ![2,0,-1,0],
  ![-1,0,-1,0]]

theorem coefficients_norm (e : Fin 28) : integerNorm (coefficients e)=1 := by
  fin_cases e <;> norm_num [coefficients,integerNorm]

@[expose] def edgeUnit (e : Fin 28) : normOneUnits :=
  ⟨unitOfNormOne (coefficients e) (coefficients_norm e),
    (mem_normOneUnits _).mpr (unitOfNormOne_norm _ _)⟩

theorem edgeUnit_value (e : Fin 28) :
    (((edgeUnit e).val:order):B)=embed (coefficients e) := rfl

@[expose] def vertex : Fin 28 → Point := ![
  ((-280/13),(-5/3)),
  ((280/13),(-5/3)),
  ((-2940/109),(-135/109)),
  ((2940/109),(-135/109)),
  ((-2100/73),(-75/73)),
  ((2100/73),(-75/73)),
  ((-175/6),(-35/36)),
  ((175/6),(-35/36)),
  ((-245/8),(-35/48)),
  ((245/8),(-35/48)),
  ((-3360/109),(-75/109)),
  ((3360/109),(-75/109)),
  ((-420/13),(-5/39)),
  ((420/13),(-5/39)),
  ((-420/13),(5/39)),
  ((420/13),(5/39)),
  ((-3360/109),(75/109)),
  ((3360/109),(75/109)),
  ((-245/8),(35/48)),
  ((245/8),(35/48)),
  ((-175/6),(35/36)),
  ((175/6),(35/36)),
  ((-2100/73),(75/73)),
  ((2100/73),(75/73)),
  ((-2940/109),(135/109)),
  ((2940/109),(135/109)),
  ((-280/13),(5/3)),
  ((280/13),(5/3))]
@[expose] def row : Fin 28 → Fin 3 → ℚ := ![
  ![8232,(1204/5),-1176],
  ![8232,(-1204/5),-1176],
  ![4200,-116,-840],
  ![4200,116,-840],
  ![8232,(1204/5),1176],
  ![8232,(-1204/5),1176],
  ![4200,-116,840],
  ![4200,116,840],
  ![672,(-104/5),0],
  ![672,(104/5),0],
  ![1125,-30,-255],
  ![1125,-30,255],
  ![980,-28,168],
  ![980,-28,-168],
  ![222,(-34/5),-18],
  ![222,(-26/5),-66],
  ![222,(26/5),-66],
  ![222,(34/5),-18],
  ![980,28,-168],
  ![980,28,168],
  ![1125,30,-255],
  ![1125,30,255],
  ![222,(-26/5),66],
  ![222,(-34/5),18],
  ![222,(26/5),66],
  ![222,(34/5),18],
  ![5,0,-3],
  ![5,0,3]]
@[expose] def sideValue (e : Fin 28) (P : Point) : ℚ := row e 0+row e 1*P.1+row e 2*P.2
@[expose] def partner : Fin 28 → Fin 28 := ![1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16,19,18,21,20,23,22,25,24,27,26]
@[expose] def start : Fin 28 → Fin 28 := ![16,17,21,20,8,9,5,4,13,12,23,3,7,19,15,25,24,14,18,6,22,2,1,11,0,10,26,0]
@[expose] def finish : Fin 28 → Fin 28 := ![18,19,23,22,10,11,7,6,15,14,25,5,9,21,17,27,26,16,20,8,24,4,3,13,2,12,27,1]
@[expose] def imageStart : Fin 28 → Fin 28 := ![17,16,20,21,9,8,4,5,12,13,5,25,21,9,27,17,16,26,8,20,4,24,13,3,12,2,0,26]
@[expose] def imageFinish : Fin 28 → Fin 28 := ![19,18,22,23,11,10,6,7,14,15,3,23,19,7,25,15,14,24,6,18,2,22,11,1,10,0,1,27]

/-- Each literal row is the SAME original-unit Klein energy row. -/
theorem row_energy (e : Fin 28) (P : Point) :
    sideValue e P=2*denominator (embed (coefficients e)) P-2 := by
  rw [denominator_value]
  fin_cases e <;> norm_num [sideValue,row,coefficients,embed] <;> ring

theorem vertex_inside (v : Fin 28) : (vertex v).1^2/1050+(vertex v).2^2/5<1 := by
  fin_cases v <;> norm_num [vertex]

theorem boundary_endpoints (e : Fin 28) :
    sideValue e (vertex (start e))=0 ∧ sideValue e (vertex (finish e))=0 := by
  fin_cases e <;> norm_num [sideValue,row,vertex,start,finish]

theorem boundary_denominators (e : Fin 28) :
    denominator (embed (coefficients e)) (vertex (start e))=1 ∧
    denominator (embed (coefficients e)) (vertex (finish e))=1 := by
  have hs := row_energy e (vertex (start e))
  have hf := row_energy e (vertex (finish e))
  obtain ⟨hs0,hf0⟩ := boundary_endpoints e
  constructor <;> linarith

/-- Exact rational projective action of each actual unit on BOTH endpoints,
not merely incidence in a polygon with the right number of vertices. -/
theorem endpoint_action (e : Fin 28) :
    action (embed (coefficients e)) (vertex (start e))=vertex (imageStart e) ∧
    action (embed (coefficients e)) (vertex (finish e))=vertex (imageFinish e) := by
  fin_cases e <;>
    norm_num [action,denominator,matrix,vector,coefficients,embed,vertex,
      start,finish,imageStart,imageFinish,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem partner_involution (e : Fin 28) : partner (partner e)=e ∧ partner e≠e := by
  fin_cases e <;> norm_num [partner]

theorem partner_endpoints (e : Fin 28) :
    ({imageStart e,imageFinish e}:Finset (Fin 28))={start (partner e),finish (partner e)} := by
  fin_cases e <;> decide
/-- Paired original units are mutual inverses up to the ORIGINAL central -1. -/
theorem paired_coordinates (e : Fin 28) :
    product (coefficients (partner e)) (coefficients e)=![-1,0,0,0] := by
  fin_cases e <;> ext k <;> fin_cases k <;> norm_num [coefficients,partner,product]

theorem paired_original_product (e : Fin 28) :
    embed (coefficients (partner e))*embed (coefficients e)=(-1:B) := by
  rw [←embed_mul,paired_coordinates]
  ext <;> norm_num [embed]

/-- Every rational point of the closed side is transported by the SAME
original unit to the corresponding point of the paired closed side. -/
theorem side_action (e : Fin 28) (s : ℚ) :
    action (embed (coefficients e))
      (mix (vertex (start e)) (vertex (finish e)) s)=
      mix (vertex (imageStart e)) (vertex (imageFinish e)) s := by
  rw [action_mix _ _ _ _ (boundary_denominators e).1 (boundary_denominators e).2,
    (endpoint_action e).1,(endpoint_action e).2]
end PELDirichletSidePairingData318
