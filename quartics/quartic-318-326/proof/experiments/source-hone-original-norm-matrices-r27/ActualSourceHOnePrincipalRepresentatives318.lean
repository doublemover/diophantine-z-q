module
public import ActualSourceHOneCoordinates318
public import ContactWholePrincipalReduction318

public section
noncomputable section
namespace ActualSourceHOnePrincipalRepresentatives318
open Polynomial RootOrderMonomialBasis318
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev units := SourceTwistArithmetic318.units
abbrev HOne := ActualSourceHOnePullbacks318.SourceHOne
abbrev boundary := ActualSourceHOneCoordinates318.boundary

/-- The actual infinity-ring image is killed by the original Mayer-Vietoris
boundary, using the original finite-minus-infinity convention. -/
theorem infinity_boundary_zero (b : InfinityOpenChart318.OpenOrder units) :
    boundary (InfinityOverlapLocalization318.toOpen units b) = 0 := by
  apply (ActualSourceHOneCoordinates318.boundary_eq_zero_iff _).mpr
  refine ⟨0,-b,?_⟩
  change SourceOpenFractionField318.orderToOpen units 0 -
    InfinityOverlapLocalization318.toOpen units (-b) = InfinityOverlapLocalization318.toOpen units b
  simp only [map_zero,map_neg,sub_neg_eq_add,zero_add]

/-- The actual finite-ring image is killed by the same unchanged boundary. -/
theorem finite_boundary_zero (a : ContactKummerOrder318.SourceOrder units) :
    boundary (SourceOpenFractionField318.orderToOpen units a) = 0 := by
  apply (ActualSourceHOneCoordinates318.boundary_eq_zero_iff _).mpr
  refine ⟨a,0,?_⟩
  change SourceOpenFractionField318.orderToOpen units a -
    InfinityOverlapLocalization318.toOpen units 0 = SourceOpenFractionField318.orderToOpen units a
  simp only [map_zero,sub_zero]

/-- One original overlap-ring principal monomial, sent to genuine source H1. -/
@[expose] def principalClass (P : ℚ[X]) (n : ℕ) (i : ThreeIndex) : HOne :=
  boundary (ContactInfinityRegularFractions318.principalTerm units P n *
    InfinityOverlapLocalization318.toOpen units (ContactHOneOrderBases318.infinityBasis units i))

/-- Every class of the actual whole source H1 has a finite principal-part
representative in all eight original infinity ratio monomials. The pole bound
may depend on the class; no uniform dimension bound is asserted. -/
theorem principal_representatives (y : HOne) :
    ∃ n : ℕ, ∃ R : ThreeIndex → ℚ[X],
      (∀ i, (R i).degree < (n : WithBot ℕ)) ∧
      y = ∑ i, principalClass (R i) n i := by
  obtain ⟨z,hz⟩ := ActualSourceHOneCoordinates318.boundary_surjective y
  obtain ⟨n,R,b,hR,hr⟩ := ContactWholePrincipalReduction318.reduction units z
  refine ⟨n,R,hR,?_⟩
  have hb : boundary (ContactWholePrincipalReduction318.inclusion units b) = 0 :=
    infinity_boundary_zero b
  calc
    y = boundary z := hz.symm
    _ = boundary ((∑ i, ContactInfinityRegularFractions318.principalTerm units (R i) n *
        ContactWholePrincipalReduction318.inclusion units
          (ContactHOneOrderBases318.infinityBasis units i)) +
        ContactWholePrincipalReduction318.inclusion units b) := congrArg boundary hr
    _ = ∑ i, principalClass (R i) n i := by
      rw [map_add,hb,add_zero,map_sum] <;> rfl

end ActualSourceHOnePrincipalRepresentatives318
