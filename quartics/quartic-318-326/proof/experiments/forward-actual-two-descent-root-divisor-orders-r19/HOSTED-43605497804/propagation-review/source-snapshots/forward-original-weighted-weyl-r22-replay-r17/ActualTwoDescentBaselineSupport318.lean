module
public import ActualTwoDescentExtendedVectors318
public section
noncomputable section
namespace ActualTwoDescentBaselineSupport318
open ActualTwoDescentBetaThetaFamily318 ActualTwoDescentSmallPattern318
open ActualTwoDescentSmallPrimeAssembly318 ActualTwoDescentSmallCore318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentFamilyProducts318
open ActualTwoDescentAdjoinedPrimes318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentMatrixCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

lemma support_coprime_of_unit {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (h : IsUnit ((∏ i, q i : ℕ) : ZMod 12)) : ∀ i, Nat.Coprime (q i) 12 := by
  have hp := (ZMod.isUnit_iff_coprime (∏ i, q i) 12).mp h
  intro i
  exact hp.of_dvd_left (Finset.dvd_prod_of_mem q (Finset.mem_univ i))

/-- The enlarged baseline is PRODUCED from the original beta/theta
support and mutual product symbols. Its old core and beta equation are
proved before any theta diagonal or replacement q0 is selected. -/
theorem actual_baseline_support (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (qB : BetaIndex d → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (hθ : ((∏ j, qJ j : ℕ) : ZMod 24)=1)
    (H : MutualSymbols qB qJ) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ F : JointFamily d qB qJ forbidden N,
      Function.Injective (fullPrimes F) ∧
      (∀ i, Nat.Coprime (fullPrimes F i) 12) ∧
      ((∏ i, assembled (betaRestriction F) i : ℕ) : ZMod 12)=11 ∧
      ((∏ i, fullPrimes F i : ℕ) : ZMod 12)=11 ∧
      Pattern d (assembled (betaRestriction F)) ∧
      laplacian (fullPrimes F) *ᵥ (extend (beta d) : Option (CoreIndex d ⊕ J) → ZMod 2)=0 ∧
      IsUnit (fun i j => sharp (fullPrimes F) (extend (selector d))
        (some (Sum.inl i)) (some (Sum.inl j)) : Matrix (CoreIndex d) (CoreIndex d) (ZMod 2)) := by
  have hβ12 : ((∏ b, qB b : ℕ) : ZMod 12)=5 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hβ
    norm_num only [map_natCast,map_ofNat] at h
    exact h
  have hθ12 : ((∏ j, qJ j : ℕ) : ZMod 12)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hθ
    simpa only [map_natCast,map_one] using h
  have hcB : ∀ b, Nat.Coprime (qB b) 12 := by
    apply support_coprime_of_unit qB
    rw [hβ12]
    exact (ZMod.unitOfCoprime 5 (by decide)).isUnit
  have hcJ : ∀ j, Nat.Coprime (qJ j) 12 := by
    apply support_coprime_of_unit qJ
    rw [hθ12]
    exact isUnit_one
  have hseedc : ∀ i, Nat.Coprime (seed qB qJ i) 12 := by
    intro i
    cases i with
    | inl b => exact hcB b
    | inr j => exact hcJ j
  have hseed2 : ∀ i, seed qB qJ i ≠ 2 := by
    intro i he
    have h := hseedc i
    rw [he] at h
    norm_num at h
  obtain ⟨F⟩ := actual_finite_family (seed qB qJ) (seed_injective qB qJ hB hJ hdis)
    hseedc hseed2 (seedBits d J) (fun _ _ => false) (fun k => decide (k=d)) forbidden N (d+1)
  have hd := full_injective F hB hJ hdis
  have hc := full_coprime F hcB hcJ
  have hs : ((∏ i, assembled (betaRestriction F) i : ℕ) : ZMod 12)=11 := by
    rw [assembled_product,Nat.cast_mul,hβ12,actual_multiplier_residue d (betaRestriction F)]
    norm_num
  have hn : ((∏ i, fullPrimes F i : ℕ) : ZMod 12)=11 := by
    change ((∏ i, adjoin (assembled (betaRestriction F)) qJ i : ℕ) : ZMod 12)=11
    rw [adjoin_product,Nat.cast_mul,hs,hθ12,mul_one]
  have HP := actual_assembled_pattern (betaRestriction F) hB hcB
  have hdsmall := assembled_injective (betaRestriction F) hB
  have hcsmall := assembled_coprime (betaRestriction F) hcB
  have hp2 : ∀ i, assembled (betaRestriction F) i ≠ 2 := by
    intro i he
    have h := hcsmall i
    rw [he] at h
    norm_num at h
  have hp3 : ∀ i, assembled (betaRestriction F) i ≠ 3 := by
    intro i he
    have h := hcsmall i
    rw [he] at h
    norm_num at h
  have hsmallbeta := actual_small_beta_kernel d (assembled (betaRestriction F)) hdsmall hp2 hs HP
  have hsmallcore := actual_small_core_unit d (assembled (betaRestriction F)) hdsmall hp2 hp3 hs HP
  obtain ⟨hcross,hnew⟩ := actual_full_cross_rows F hB hJ hdis hcB hcJ H
  have hrestrict : restricted (fullPrimes F)=assembled (betaRestriction F) := restricted_adjoin _ _
  have hfullbeta : laplacian (fullPrimes F) *ᵥ
      (extend (beta d) : Option (CoreIndex d ⊕ J) → ZMod 2)=0 := by
    apply actual_extended_kernel _ (beta d) rfl _ hcross
    · rw [hrestrict]
      exact hsmallbeta
    · intro j
      simpa only [Fintype.sum_sum_type,beta,mul_one,mul_zero,Finset.sum_const_zero,add_zero,
        oldEmbedding,bIndex] using hnew j
  have hcore : IsUnit (fun i j => sharp (fullPrimes F) (extend (selector d))
      (some (Sum.inl i)) (some (Sum.inl j)) : Matrix (CoreIndex d) (CoreIndex d) (ZMod 2)) := by
    rw [actual_old_core_preserved _ _ hcross,hrestrict,restrictedSelector_extend]
    exact hsmallcore
  exact ⟨F,hd,hc,hs,hn,HP,hfullbeta,hcore⟩

end ActualTwoDescentBaselineSupport318
