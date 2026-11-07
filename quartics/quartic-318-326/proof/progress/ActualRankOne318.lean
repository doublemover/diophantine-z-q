module
public import ActualFreePart318
public import GlobalReductionCounts318
public section
namespace ActualRankOne318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 ActualFreePart318
set_option maxHeartbeats 0
noncomputable section

theorem R_free_nonzero : quotientMap R≠0 := by
  intro hz
  have ht: IsOfFinAddOrder R:=(quotientMap_zero_iff R).mp hz
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_zsmul_eq_zero.mp ht
  exact GlobalReductionCounts318.R_infinite_order n hn he

theorem free_rank_one (ht:∀Q:E.Point,IsOfFinAddOrder Q → Q+Q=0) : Module.finrank ℤ FreePart=1 := by
  letI : Nontrivial FreePart:=⟨⟨quotientMap R,0,R_free_nonzero⟩⟩
  have hpos:0<Module.finrank ℤ FreePart:=(Module.finrank_pos_iff_of_free ℤ FreePart).mpr inferInstance
  have hle:=free_rank_le_one ht
  omega

/-- An actual generator of the free quotient, lifted to an actual point;
all remainders are actual 2-torsion. -/
theorem generator_mod_torsion (ht:∀Q:E.Point,IsOfFinAddOrder Q → Q+Q=0) :
    ∃G:E.Point,∀Q:E.Point,∃(n:ℤ)(V:E.Point),V+V=0 ∧ Q=n • G+V := by
  let b:=Module.finBasisOfFinrankEq ℤ FreePart (free_rank_one ht)
  obtain ⟨G,hG⟩:∃G:E.Point,quotientMap G=b 0 := (Submodule.torsion ℤ E.Point).mkQ_surjective _
  refine ⟨G,?_⟩
  intro Q
  let n:ℤ:=(b.repr (quotientMap Q)) 0
  have he:n • b 0=quotientMap Q := by simpa [n] using b.sum_repr (quotientMap Q)
  let V:=Q-n • G
  have hv:quotientMap V=0 := by
    simp only [V,map_sub,map_zsmul,hG,he,sub_self]
  refine ⟨n,V,ht V ((quotientMap_zero_iff V).mp hv),?_⟩
  dsimp [V]
  abel

/-- The exact rank-one/odd-index interface, derived from proved finite
quotient, finite generation, actual R infinite order and torsion control. -/
theorem odd_rank_one (ht:∀Q:E.Point,IsOfFinAddOrder Q → Q+Q=0) : GlobalSaturationLogic318.OddRankOneData := by
  obtain ⟨G,hG⟩:=generator_mod_torsion ht
  obtain ⟨m,U,hU,he⟩:=hG R
  exact ⟨G,U,m,hU,he,GlobalTorsionOddIndex318.odd_index_of_representation G U m hU he,hG⟩

end
end ActualRankOne318
#print axioms ActualRankOne318.odd_rank_one
