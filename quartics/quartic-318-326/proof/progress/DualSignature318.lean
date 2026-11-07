module
public import DualSeven318
public section
namespace DualSignature318
open ConcreteG8Domain
set_option maxHeartbeats 0

/-- Evenness at each actual normalized split place, including both places
above7, with the ramified dyadic place handled separately. -/
theorem dual_split_even (p:ℕ) [Fact p.Prime] (hp2:p≠2)
    (rho:ℚ_[p]) (hr:rho^2=2) (X Y:K) (m:ℤ)
    (hX:ConcretePadic318.place p rho hr X=m) (he:Y^2=X^3+4*D*X) : Even m := by
  by_cases hp7:p=7
  · subst p
    exact DualSeven318.dual_seven_even rho hr X Y m hX he
  have h2:¬p∣2 := by
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp hd)
  have h7:¬p∣7 := by
    intro hd
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) (by decide:Nat.Prime 7)).mp hd)
  exact DualLocalArithmetic318.dual_away_two_seven_even _ X Y m hX
    (SourcePadic318.place_nat_unit p rho hr 2 h2)
    (SourcePadic318.place_nat_unit p rho hr 7 h7) he

/-- Evenness at every actual normalized inert place. The nonsquare residue
condition itself excludes both2 and7. -/
theorem dual_inert_even (p:ℕ) [Fact p.Prime]
    (nonsquare:¬∃x:ZMod p,x^2=2) (X Y:K) (m:ℤ)
    (hX:InertPlace318.place p nonsquare X=m) (he:Y^2=X^3+4*D*X) : Even m := by
  have h7:¬p∣7 := by
    intro hd
    have hp7:p=7 := (Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) (by decide:Nat.Prime 7)).mp hd
    subst p
    exact nonsquare DualSeven318.residue_two_square
  exact DualLocalArithmetic318.dual_away_two_seven_even _ X Y m hX
    (InertPlace318.place_two p nonsquare)
    (InertSourceExclusion318.place_nat_unit p nonsquare 7 h7) he

/-- A concrete arithmetic signature of an element, not a source predicate.
The remaining global theorem is that this signature forces a square in K. -/
structure SquareSignature (X:K) : Prop where
  nonzero:X≠0
  real_positive:∀(s:ℝ)(hs:s^2=2),0<FiniteScale318.realPlace s hs X
  dyadic_even:∀m:ℤ,RamifiedTwo318.place X=m → Even m
  split_even:∀(p:ℕ)[Fact p.Prime],p≠2 → ∀(rho:ℚ_[p])(hr:rho^2=2)(m:ℤ),
    ConcretePadic318.place p rho hr X=m → Even m
  inert_even:∀(p:ℕ)[Fact p.Prime](nonsquare:¬∃x:ZMod p,x^2=2)(m:ℤ),
    InertPlace318.place p nonsquare X=m → Even m

/-- All local and real assertions of the actual dual descent are derived
from its curve equation. No finite-place parity or residue input remains. -/
theorem dual_signature (X Y:K) (he:Y^2=X^3+4*D*X) (hX:X≠0) : SquareSignature X where
  nonzero:=hX
  real_positive:=DualLocalArithmetic318.dual_real_positive X Y he hX
  dyadic_even:=fun m hm=>DualLocalArithmetic318.dual_two_even X Y m hm he
  split_even:=fun p _ hp rho hr m hm=>dual_split_even p hp rho hr X Y m hm he
  inert_even:=fun p _ nonsquare m hm=>dual_inert_even p nonsquare X Y m hm he

end DualSignature318
#print axioms DualSignature318.dual_split_even
#print axioms DualSignature318.dual_inert_even
#print axioms DualSignature318.dual_signature
