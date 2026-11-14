module
public import ActualTwoDescentActualLocalClassBound318
public section
noncomputable section
namespace ActualTwoDescentThreeUnitPoints318
open ActualTwoDescentThreeAdicTorsion318 ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentRepresentedSupport318
set_option maxHeartbeats 16000000

/-- Every unit first class has an actual Q3 curve point with square second
coordinate for n=2mod3. The two nonzero residues are handled by explicit
identity/first-torsion point constructions and actual Hensel roots. -/
theorem actual_three_unit_point (M n : ℕ) (hM : Nat.Coprime M 3)
    (hn : (n : ZMod 3)=2) : Nonempty (LocalKummerPoint (p:=3) M n) := by
  have hMn : (M : ZMod 3) ≠ 0 := ((ZMod.isUnit_iff_coprime M 3).mpr hM).ne_zero
  have hM0 : M ≠ 0 := by intro he; exact hMn (by rw [he,Nat.cast_zero])
  have hn0 : n ≠ 0 := by intro he; norm_num [he] at hn
  have hnc : (n : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hcases : (M : ZMod 3)=1 ∨ (M : ZMod 3)=2 := by
    have h : ∀ z : ZMod 3, z ≠ 0 → z=1 ∨ z=2 := by decide
    exact h _ hMn
  rcases hcases with h1 | h2
  · obtain ⟨r,hr⟩ := actual_three_adic_one_square M h1
    have hr0 : r ≠ 0 := by
      intro he
      rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr
      exact (Nat.cast_ne_zero.mpr hM0) hr.symm
    exact actual_local_kummer_of_square M n r hr0 hr
  · have hprod : ((M*n : ℕ) : ZMod 3)=1 := by rw [Nat.cast_mul,h2,hn]; norm_num
    obtain ⟨s,hs⟩ := actual_three_adic_one_square (M*n) hprod
    have hs0 : s ≠ 0 := by
      intro he
      rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      exact (Nat.cast_ne_zero.mpr (mul_ne_zero hM0 hn0)) hs.symm
    apply actual_local_kummer_of_first_torsion M n hn0 (s/n) (div_ne_zero hs0 hnc)
    rw [div_pow,hs,Nat.cast_mul]
    field_simp [hnc]
    <;> ring

lemma actual_local_kummer_represented {q : ℕ} [Fact q.Prime] (M n : ℕ)
    (H : Nonempty (LocalKummerPoint (p:=q) M n)) : RepresentedAt q n M 1 := by
  obtain ⟨P⟩ := H
  refine ⟨P.point,P.u,P.v,P.u_ne,P.v_ne,P.first,?_⟩
  simpa only [Nat.cast_one,one_mul] using P.second

end ActualTwoDescentThreeUnitPoints318
