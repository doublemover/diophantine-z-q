module
public import FiniteSieveFirstOrder318
public section
noncomputable section
namespace FixedSieveExceptionalPrimes318
open FiniteSieveDensity318 OriginalSieveResidueDensity318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def pairs : Finset (ι×ι) := Finset.univ.filter (fun ij => ij.1≠ij.2)
@[expose] def differences (γ : ι → ℤ) : ℕ := ∏ ij∈(pairs (ι:=ι)),(γ ij.2-γ ij.1).natAbs
@[expose] def exceptionalProduct (κ : ℤ) (γ : ι → ℤ) : ℕ := 2*κ.natAbs*differences γ
@[expose] def exceptionalPrimes (κ : ℤ) (γ : ι → ℤ) : Finset ℕ :=
  (exceptionalProduct κ γ).primeFactors

lemma product_positive (κ : ℤ) (hκ : κ≠0) (γ : ι → ℤ) (hγ : Function.Injective γ) :
    0<exceptionalProduct κ γ := by
  have hd : 0<differences γ := by
    apply Finset.prod_pos
    intro ij hij
    have hne : ij.1≠ij.2 := (Finset.mem_filter.mp hij).2
    apply Int.natAbs_pos.mpr
    intro he
    exact hne (hγ (sub_eq_zero.mp he)).symm
  dsimp [exceptionalProduct]
  exact mul_pos (mul_pos (by norm_num) (Int.natAbs_pos.mpr hκ)) hd

lemma nat_dvd_of_int_dvd (p : ℕ) (n : ℤ) (h : (p:ℤ)∣n) : p∣n.natAbs := by
  obtain ⟨k,rfl⟩ := h
  exact ⟨k.natAbs,by simp only [Int.natAbs_mul,Int.natAbs_natCast]⟩

/-- A single explicitly constructed finite exceptional set supplies every
original nondegeneracy and distinct-residue condition, uniformly in later limits. -/
theorem outside_conditions (κ : ℤ) (hκ : κ≠0) (γ : ι → ℤ) (hγ : Function.Injective γ)
    (p : ℕ) (hp : p.Prime) (hout : p∉exceptionalPrimes κ γ) :
    p≠2 ∧ ¬(p:ℤ)∣κ ∧ ∀ i j, i≠j → ¬(p:ℤ)∣γ j-γ i := by
  have hn : exceptionalProduct κ γ≠0 := Nat.ne_of_gt (product_positive κ hκ γ hγ)
  have hnot : ¬p∣exceptionalProduct κ γ := by
    intro hd
    exact hout (Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩)
  have hd2 : 2∣exceptionalProduct κ γ := ⟨κ.natAbs*differences γ,by dsimp [exceptionalProduct]; ring⟩
  have hdk : κ.natAbs∣exceptionalProduct κ γ := ⟨2*differences γ,by dsimp [exceptionalProduct]; ring⟩
  refine ⟨?_,?_,?_⟩
  · intro he
    subst p
    exact hnot hd2
  · intro hd
    exact hnot ((nat_dvd_of_int_dvd p κ hd).trans hdk)
  · intro i j hij hd
    have hm : (i,j)∈pairs (ι:=ι) := by simp [pairs,hij]
    have hdij : (γ j-γ i).natAbs∣differences γ := Finset.dvd_prod_of_mem _ hm
    have hf : differences γ∣exceptionalProduct κ γ := dvd_mul_left _ _
    exact hnot ((nat_dvd_of_int_dvd p (γ j-γ i) hd).trans (hdij.trans hf))

/-- The actual original density estimate is now available at EVERY prime
outside the constructed fixed set, rather than a separately supplied family. -/
theorem outside_density_error (κ : ℤ) (hκ : κ≠0) (γ : ι → ℤ) (hγ : Function.Injective γ)
    (i₀ i₁ : ι) (h0 : γ i₀=0) (h1 : γ i₁= -κ)
    (p : ℕ) [Fact p.Prime] (hout : p∉exceptionalPrimes κ γ) :
    |density (κ:ZMod p) (fun i => (γ i:ZMod p)) i₀-
      ((Fintype.card ι:ℚ)+2*(quadraticChar (ZMod p) (-1:ZMod p):ℚ))/(p:ℚ)|≤
      4*((Fintype.card ι:ℚ)+1)/(p:ℚ)^2 := by
  obtain ⟨hp2,hkp,havoid⟩ := outside_conditions κ hκ γ hγ p (Fact.out : p.Prime) hout
  have hF : ringChar (ZMod p)≠2 := by simpa only [ringChar_zmod_n] using hp2
  have hk : (κ:ZMod p)≠0 := by intro he; exact hkp ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  have hc0 : (γ i₀:ZMod p)=0 := by rw [h0,Int.cast_zero]
  have hc1 : (γ i₁:ZMod p)= -(κ:ZMod p) := by rw [h1,Int.cast_neg]
  simpa only [ZMod.card] using FiniteSieveFirstOrder318.actual_error hF
    (GoodReductionResidue318.two_residue_ne p hp2) (κ:ZMod p) hk
    (fun i => (γ i:ZMod p)) (residue_injective p γ havoid) i₀ i₁ hc0 hc1

end FixedSieveExceptionalPrimes318
