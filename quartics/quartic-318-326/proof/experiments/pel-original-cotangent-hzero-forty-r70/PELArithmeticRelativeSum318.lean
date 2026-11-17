module
public import PELJointRelativeAddition318
public section
noncomputable section
namespace PELArithmeticRelativeSum318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELJointArithmeticLift318 PELOriginalUnitBiholomorph318 PELPrincipalThreeFreeAction318
open PELPrincipalProperAction318 PELPrincipalThreeCovering318 PELArithmeticOriginalFibers318
open PELJointRelativeAddition318
set_option maxHeartbeats 1800000

theorem relativeAdd_equivariant (u : principalThree) (p q : Total) (hbase : p.1=q.1) :
    u • relativeAdd p q=relativeAdd (u • p) (u • q) := by
  rcases p with ⟨τ,z⟩
  rcases q with ⟨σ,w⟩
  change τ=σ at hbase
  subst σ
  change (nextParameter u.val (determinant u) τ,
    fiberEquiv _ (transport u.val (determinant u) τ τ.property
      ((fiberEquiv τ).symm (z+w))))=
    (nextParameter u.val (determinant u) τ,
      fiberEquiv _ (transport u.val (determinant u) τ τ.property ((fiberEquiv τ).symm z))+
      fiberEquiv _ (transport u.val (determinant u) τ τ.property ((fiberEquiv τ).symm w)))
  rw [map_add,map_add,map_add]

/-- A sum is represented by TWO actual original points with the same
parameter; this relation uses no choice of arithmetic base representative. -/
@[expose] def SumRelation (p q r : ArithmeticTotal) : Prop :=
  ∃ x y : Total,totalQuotient x=p ∧ totalQuotient y=q ∧ x.1=y.1 ∧
    totalQuotient (relativeAdd x y)=r

theorem sum_exists (p q : ArithmeticTotal)
    (hbase : arithmeticProjection p=arithmeticProjection q) : ∃ r, SumRelation p q r := by
  obtain ⟨x,hx⟩ := totalQuotient_surjective p
  obtain ⟨y,hy⟩ := totalQuotient_surjective q
  have hb : baseQuotient x.1=baseQuotient y.1 := by
    simpa only [←hx,←hy,arithmetic_projection_square] using hbase
  obtain ⟨u,hu⟩ := base_covering.apply_eq_iff_mem_orbit.mp hb
  refine ⟨totalQuotient (relativeAdd x (u • y)),x,u • y,hx,?_,?_,rfl⟩
  · exact (total_covering.map_smul u).trans hy
  · exact ((projection_smul u y).trans hu).symm

/-- Exact base freeness forces the SAME arithmetic element to compare
both members of two aligned pairs. Hence the relative sum is independent
of every representative and orbit-lifting choice. -/
theorem sum_unique {p q r s : ArithmeticTotal}
    (hr : SumRelation p q r) (hs : SumRelation p q s) : r=s := by
  obtain ⟨x,y,hx,hy,hxy,hr⟩ := hr
  obtain ⟨x',y',hx',hy',hxy',hs⟩ := hs
  obtain ⟨u,hu⟩ := total_covering.apply_eq_iff_mem_orbit.mp (hx.trans hx'.symm)
  obtain ⟨v,hv⟩ := total_covering.apply_eq_iff_mem_orbit.mp (hy.trans hy'.symm)
  have huv : u=v := by
    have h : u • x'.1=v • x'.1 := by
      calc
        _ = x.1 := (projection_smul u x').symm.trans (congrArg Prod.fst hu)
        _ = y.1 := hxy
        _ = v • y'.1 := ((projection_smul v y').symm.trans (congrArg Prod.fst hv)).symm
        _ = v • x'.1 := congrArg (fun t => v • t) hxy'.symm
    exact IsCancelSMul.right_cancel u v x'.1 h
  subst v
  calc
    r = totalQuotient (relativeAdd x y) := hr.symm
    _ = totalQuotient (relativeAdd (u • x') (u • y')) := by rw [hu,hv]
    _ = totalQuotient (u • relativeAdd x' y') :=
      congrArg totalQuotient (relativeAdd_equivariant u x' y' hxy').symm
    _ = totalQuotient (relativeAdd x' y') := total_covering.map_smul u
    _ = s := hs

/-- The actual relative fiber product of the arithmetic projection. -/
abbrev RelativePair := {p : ArithmeticTotal × ArithmeticTotal //
  arithmeticProjection p.1=arithmeticProjection p.2}
@[expose] def arithmeticAdd (p : RelativePair) : ArithmeticTotal :=
  (sum_exists p.val.1 p.val.2 p.property).choose

theorem arithmeticAdd_relation (p : RelativePair) : SumRelation p.val.1 p.val.2 (arithmeticAdd p) :=
  (sum_exists p.val.1 p.val.2 p.property).choose_spec

theorem arithmeticAdd_square (x y : Total) (hxy : x.1=y.1) :
    arithmeticAdd ⟨(totalQuotient x,totalQuotient y),congrArg baseQuotient hxy⟩=
      totalQuotient (relativeAdd x y) :=
  sum_unique (arithmeticAdd_relation _) ⟨x,y,rfl,rfl,hxy,rfl⟩

theorem arithmeticAdd_over_base (p : RelativePair) :
    arithmeticProjection (arithmeticAdd p)=arithmeticProjection p.val.1 := by
  obtain ⟨x,y,hx,hy,hxy,hr⟩ := arithmeticAdd_relation p
  rw [←hr,←hx,arithmetic_projection_square,arithmetic_projection_square]
  all_goals rfl
end PELArithmeticRelativeSum318
