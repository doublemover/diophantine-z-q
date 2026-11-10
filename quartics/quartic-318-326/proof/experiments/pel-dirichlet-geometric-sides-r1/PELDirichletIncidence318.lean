module
public import PELDirichletVertexFan318
public section
noncomputable section
namespace PELDirichletIncidence318
open PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318 PELDirichletSidePairingData318
set_option maxHeartbeats 1800000

@[expose] def selection : Fin 28 → Fin 8 × Bool × Bool := ![(2,true,false),(2,false,false),(4,false,false),(4,true,false),(2,true,true),(2,false,true),(4,false,true),(4,true,true),(0,false,false),(0,true,false),(5,false,false),(5,false,true),(3,false,true),(3,false,false),(1,false,false),(6,false,false),(6,true,false),(1,true,false),(3,true,false),(3,true,true),(5,true,false),(5,true,true),(6,false,true),(1,false,true),(6,true,true),(1,true,true),(7,false,false),(7,false,true)]
@[expose] def centralSign : Fin 28 → ℤ := ![-1,1,1,-1,1,-1,-1,1,1,-1,1,1,1,1,1,1,-1,-1,-1,-1,-1,-1,1,1,1,1,1,1]

/-- Exact full integer-coordinate identification with the actual signed
energy-test unit; the central sign is retained, not silently discarded. -/
theorem selected_coefficients (e : Fin 28) :
    coefficients e=centralSign e •
      signedCoefficients (selection e).1 (selection e).2.1 (selection e).2.2 := by
  fin_cases e <;> ext k <;> fin_cases k <;>
    norm_num [coefficients,centralSign,selection,signedCoefficients,
      baseCoefficients,flipFirst,flipSecond]

theorem centralSign_square (e : Fin 28) : centralSign e ^ 2=1 := by
  fin_cases e <;> norm_num [centralSign]

/-- Every listed vertex is in every literal original half-plane. -/
theorem vertex_all_rows (v e : Fin 28) : 0≤sideValue e (vertex v) := by
  fin_cases v <;> fin_cases e <;> norm_num [sideValue,row,vertex]

/-- All32 original signed energy inequalities, including repeated axis
rows, hold at every original vertex. -/
theorem vertex_all_signed_rows (v : Fin 28) (j : Fin 8) (ε δ : Bool) :
    rowFirst j*sign ε*(vertex v).1+rowSecond j*sign δ*(vertex v).2≤rowConstant j := by
  fin_cases v <;> fin_cases j <;> cases ε <;> cases δ <;>
    norm_num [rowFirst,rowSecond,rowConstant,sign,vertex]
end PELDirichletIncidence318
