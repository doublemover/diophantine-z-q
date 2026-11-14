module
public import ActualTwoDescentPrimaryBaerExtension318
public section
noncomputable section
namespace ActualTwoDescentPrimaryInvolutionDetection318
set_option maxHeartbeats 16000000

variable {G H : Type*} [CommGroup G] [CommGroup H]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every nonidentity primary element has an ACTUAL nonidentity involution among its powers. -/
lemma actual_nonzero_primary_involution (hP : IsPGroup 2 G) (x : G) (hx : x ≠ 1) :
    ∃ k : ℕ, (x^(2^k))^2=1 ∧ x^(2^k) ≠ 1 := by
  obtain ⟨k,hk⟩ := IsPGroup.iff_orderOf.mp hP x
  cases k with
  | zero =>
    have ho : orderOf x=1 := by simpa using hk
    exact (hx (orderOf_eq_one_iff.mp ho)).elim
  | succ k =>
    refine ⟨k,?_,?_⟩
    · rw [←pow_mul,←pow_succ,←hk]
      exact pow_orderOf_eq_one x
    · intro h
      have hd : 2^(k+1) ∣ 2^k := by rw [←hk]; exact orderOf_dvd_of_pow_eq_one h
      have hle := Nat.le_of_dvd (show 0<2^k from pow_pos (by decide) k) hd
      have hpow : 2^(k+1)=2^k*2 := pow_succ 2 k
      have hp : 0<2^k := pow_pos (by decide) k
      omega

lemma actual_primary_injective_of_involution_injective (hP : IsPGroup 2 G) (f : G →* H)
    (ht : ∀ x : G, x^2=1 → f x=1 → x=1) : Function.Injective f := by
  intro x y h
  apply div_eq_one.mp
  by_contra hxy
  obtain ⟨k,hk,hne⟩ := actual_nonzero_primary_involution hP (x/y) hxy
  apply hne
  apply ht _ hk
  rw [map_pow,map_div,h,div_self,one_pow]

end ActualTwoDescentPrimaryInvolutionDetection318
