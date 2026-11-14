module
public import ActualTwoDescentActualShaAlternatingQuotient318
public section
noncomputable section
namespace ActualTwoDescentCyclicLevelSquareRoot318
set_option maxHeartbeats 16000000

variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- In a finite cyclic2-group, every element killed below the maximal order is an ACTUAL square. -/
lemma actual_square_below_larger_order (hP : IsPGroup 2 G) (k : ℕ) (x y : G)
    (hx : x^(2^k)=1) (hy : y^(2^k) ≠ 1) : ∃ z : G, z^2=x := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_monoid_generator (α:=G)
  obtain ⟨m,hm⟩ := (IsPGroup.iff_orderOf.mp hP) g
  have hkm : k<m := by
    by_contra h
    have hd : orderOf g ∣ 2^k := by rw [hm]; exact Nat.pow_dvd_pow 2 (by omega)
    have hgk := orderOf_dvd_iff_pow_eq_one.mp hd
    obtain ⟨j,rfl⟩ := hg y
    apply hy
    rw [←pow_mul,Nat.mul_comm j (2^k),pow_mul,hgk,one_pow]
  obtain ⟨i,hi⟩ := hg x
  have hiorder : 2^m ∣ i*2^k := by
    rw [←hm]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul,hi,hx]
  have hd : 2^(k+1) ∣ i*2^k := (Nat.pow_dvd_pow 2 (by omega)).trans hiorder
  obtain ⟨a,ha⟩ := hd
  have hi2 : i=2*a := by
    apply Nat.eq_of_mul_eq_mul_right (show 0<2^k from pow_pos (by decide) k)
    calc
      i*2^k=2^(k+1)*a := ha
      _=(2*a)*2^k := by rw [pow_succ]; ring
  refine ⟨g^a,?_⟩
  rw [←pow_mul,Nat.mul_comm a 2,←hi2,hi]

end ActualTwoDescentCyclicLevelSquareRoot318
