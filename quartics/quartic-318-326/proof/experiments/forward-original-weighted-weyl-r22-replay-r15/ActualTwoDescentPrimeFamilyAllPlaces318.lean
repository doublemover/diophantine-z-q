module
public import ActualTwoDescentAllPlacesBetaClass318
public section
noncomputable section
namespace ActualTwoDescentPrimeFamilyAllPlaces318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimeMonomials318 ActualTwoDescentAllPlacesBetaClass318
open ActualTwoDescentLocalKummerWitness318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentTorsionKummerValues318
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_monomial_divides_product (p : ι → ℕ) (u : ι → ZMod 2) : monomial p u ∣ ∏ i, p i := by
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  have hu : (u i).val < 2 := ZMod.val_lt _
  have he : (u i).val=0 ∨ (u i).val=1 := by omega
  rcases he with he|he <;> simp only [he,pow_zero,pow_one,one_dvd,dvd_refl]

lemma actual_prime_divides_family (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (q : ℕ) [Fact q.Prime] (h : q ∣ ∏ i, p i) : ∃ i, q=p i := by
  have H : ∀ s : Finset ι, q ∣ ∏ i ∈ s, p i → ∃ i ∈ s, q ∣ p i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hd
      have he : q=1 := Nat.dvd_one.mp (by simpa only [Finset.prod_empty] using hd)
      exact False.elim ((Fact.out : q.Prime).ne_one he)
    | @insert i s hi ih =>
      intro hd
      rw [Finset.prod_insert hi] at hd
      rcases (Fact.out : q.Prime).dvd_mul.mp hd with hdi|hds
      · exact ⟨i,Finset.mem_insert_self _ _,hdi⟩
      · obtain ⟨j,hj,hdj⟩ := ih hds
        exact ⟨j,Finset.mem_insert_of_mem hj,hdj⟩
  obtain ⟨i,_,hi⟩ := H Finset.univ h
  exact ⟨i,(Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hi⟩

lemma actual_family_all_places (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (β : ℕ) (hβ : β ≠ 0) (hdiv : β ∣ ∏ i, p i)
    (h2 : Nonempty (LocalKummerPoint (p:=2) β (∏ i, p i)))
    (h3 : Nonempty (LocalKummerPoint (p:=3) β (∏ i, p i)))
    (hbad : ∀ i, Nonempty (LocalKummerPoint (p:=p i) β (∏ j, p j))) :
    retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hβ) ∈
      allPlacesImage ((∏ i, p i : ℕ) : ℚ)
        (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (p i).Prime).ne_zero))) := by
  apply actual_all_places_beta _ β _ hβ hdiv h2 h3
  intro q hq hqn
  obtain ⟨i,hi⟩ := actual_prime_divides_family p q hqn
  subst q
  exact hbad i

end ActualTwoDescentPrimeFamilyAllPlaces318
