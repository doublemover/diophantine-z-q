module
public import ActualTwoDescentLocalFirstTorsionPoint318
public section
noncomputable section
namespace ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentLocalIdentityPoint318 ActualTwoDescentLocalFirstTorsionPoint318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- Actual LOCAL curve and square-root coordinates for the retained beta
Kummer class. The completed field is explicit; this is not a rational point. -/
structure LocalKummerPoint (β n : ℕ) where
  point : LocalPoint (p:=p) n
  u : ℚ_[p]
  v : ℚ_[p]
  u_ne : u ≠ 0
  v_ne : v ≠ 0
  first : point.x+3*n=(β : ℚ_[p])*u^2
  second : point.x-n=v^2

/-- Transport a constructed torsion-class local point by an actual
nonzero square witness at the same prime. -/
theorem actual_local_kummer_transport (β n : ℕ) (P : LocalPoint (p:=p) n)
    (c : ℚ_[p]) (H : SquarePair (P.x+3*n) (P.x-n) c 1)
    (r : ℚ_[p]) (hr : r ≠ 0) (hβ : (β : ℚ_[p])=c*r^2) :
    Nonempty (LocalKummerPoint (p:=p) β n) := by
  obtain ⟨u,v,hu,hv,hA,hB⟩ := H
  refine ⟨⟨P,u/r,v,div_ne_zero hu hr,hv,?_,?_⟩⟩
  · rw [hA,hβ,div_pow]
    field_simp [hr]
    <;> ring
  · simpa only [one_mul] using hB

theorem actual_local_kummer_of_square (β n : ℕ) (r : ℚ_[p]) (hr : r ≠ 0)
    (hβ : r^2=(β : ℚ_[p])) : Nonempty (LocalKummerPoint (p:=p) β n) := by
  obtain ⟨P,H⟩ := actual_identity_local_point (p:=p) n
  exact actual_local_kummer_transport β n P 1 H r hr (by simpa only [one_mul] using hβ.symm)

theorem actual_local_kummer_of_first_torsion (β n : ℕ) (hn : n ≠ 0)
    (r : ℚ_[p]) (hr : r ≠ 0) (hβ : (β : ℚ_[p])=(n : ℚ_[p])*r^2) :
    Nonempty (LocalKummerPoint (p:=p) β n) := by
  obtain ⟨P,H⟩ := actual_first_torsion_local_point (p:=p) n hn
  exact actual_local_kummer_transport β n P n H r hr hβ

end ActualTwoDescentLocalKummerWitness318
