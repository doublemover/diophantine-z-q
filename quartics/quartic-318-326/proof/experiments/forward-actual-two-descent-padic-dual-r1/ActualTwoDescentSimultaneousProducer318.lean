module
public import ActualTwoDescentFiniteConclusion318
public section
noncomputable section
namespace ActualTwoDescentSimultaneousProducer318
open ActualTwoDescentSmallPattern318 ActualTwoDescentSmallPrimeAssembly318
open ActualTwoDescentSmallCore318 ActualTwoDescentBetaThetaFamily318
open ActualTwoDescentBaselineSupport318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentMatrixCompletion318
open ActualTwoDescentSimultaneousCoreChoice318 ActualTwoDescentQ0BetaPreservation318
open ActualTwoDescentRetainedSmallPattern318 ActualTwoDescentFiniteConclusion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Produce BOTH finite descent packages from the original beta/theta
data, at one actual final q0 and exactly n,n*theta. Every auxiliary prime,
pattern, baseline core, beta equation and enlarged diagonal choice is
constructed. The global Selmer/Kummer rational-point step is still separate. -/
theorem actual_simultaneous_finite_descent (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (qB : BetaIndex d → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hβ : ((∏ b, qB b : ℕ) : ZMod 24)=17) (hθ : ((∏ j, qJ j : ℕ) : ZMod 24)=1)
    (H : MutualSymbols qB qJ) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ p' : Option (CoreIndex d ⊕ J) → ℕ,
      (∀ i, (p' i).Prime) ∧ Function.Injective p' ∧
      (∀ b, p' (some (Sum.inl (Sum.inl b)))=qB b) ∧
      (∀ j, p' (some (Sum.inr j))=qJ j) ∧ p' none ∉ forbidden ∧
      (∏ i, p' i)=(∏ i, restricted p' i)*(∏ j, qJ j) ∧
      Conclusion (restricted p') (selector d) (beta d) N ∧
      Conclusion p' (extend (selector d)) (extend (beta d)) N := by
  classical
  obtain ⟨F,hd,hc,hnSmall,hn,HP,hbeta,hcore⟩ :=
    actual_baseline_support d qB qJ hB hJ hdis hβ hθ H forbidden N
  have htype : (fullPrimes F none : ZMod 12)=7 := assembled_type_Q (betaRestriction F)
  obtain ⟨p',hp',hd',hfix,hlarge,havoid,hfresh,htype',hn',hunit',hcorefix,holdbits⟩ :=
    actual_simultaneous_core_choice (fullPrimes F) hd hc htype hn
      (extend (selector d)) hcore forbidden N
  letI : ∀ i, Fact (p' i).Prime := fun i => ⟨hp' i⟩
  letI : ∀ i : Index d, Fact (restricted p' i).Prime := fun i => ⟨hp' (oldEmbedding i)⟩
  have hc' : ∀ i, Nat.Coprime (p' i) 12 := by
    intro i
    cases i with
    | none =>
      apply (ZMod.isUnit_iff_coprime (p' none) 12).mp
      rw [htype']
      exact (ZMod.unitOfCoprime 7 (by decide)).isUnit
    | some i => rw [hfix]; exact hc (some i)
  have hp2' : ∀ i, p' i ≠ 2 := by
    intro i he
    have h := hc' i
    rw [he] at h
    norm_num at h
  have hθfixed : ∀ j, p' (some (Sum.inr j))=qJ j := fun j => hfix (Sum.inr j)
  have hβfixed : ∀ b, p' (some (Sum.inl (Sum.inl b)))=qB b :=
    fun b => hfix (Sum.inl (Sum.inl b))
  have hfactor : (∏ i, p' i)=(∏ i, restricted p' i)*(∏ j, qJ j) := by
    rw [actual_product_split]
    simp_rw [hθfixed]
  have hθ12 : ((∏ j, qJ j : ℕ) : ZMod 12)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hθ
    simpa only [map_natCast,map_one] using h
  have hnSmall' : ((∏ i, restricted p' i : ℕ) : ZMod 12)=11 := by
    have h := hn'
    rw [hfactor,Nat.cast_mul,hθ12,mul_one] at h
    exact h
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hdSmall : Function.Injective (restricted p') := hd'.comp hemb
  have hcSmall : ∀ i : Index d, Nat.Coprime (restricted p' i) 12 :=
    fun i => hc' (oldEmbedding i)
  have hp2Small : ∀ i : Index d, restricted p' i ≠ 2 := fun i => hp2' (oldEmbedding i)
  have hp3Small : ∀ i : Index d, restricted p' i ≠ 3 := by
    intro i he
    have h := hcSmall i
    rw [he] at h
    norm_num at h
  have hfixSmall : ∀ i : CoreIndex d,
      restricted p' (some i)=assembled (betaRestriction F) (some i) :=
    fun i => hfix (Sum.inl i)
  have hbitsSmall : ∀ i : CoreIndex d,
      edges (restricted p') (some i) none=
        edges (assembled (betaRestriction F)) (some i) none := by
    intro i
    calc
      edges (restricted p') (some i) none=
          edges p' (some (Sum.inl i)) none := actual_restricted_edges p' (some i) none
      _=edges (fullPrimes F) (some (Sum.inl i)) none := holdbits i
      _=edges (assembled (betaRestriction F)) (some i) none :=
        (actual_restricted_edges (fullPrimes F) (some i) none).symm
  have HP' : Pattern d (restricted p') := actual_small_pattern_retained d
    (assembled (betaRestriction F)) (restricted p') hfixSmall hbitsSmall htype' HP
  have hbSmall := actual_small_beta_kernel d (restricted p') hdSmall hp2Small hnSmall' HP'
  have huSmall := actual_small_core_unit d (restricted p') hdSmall hp2Small hp3Small hnSmall' HP'
  have Csmall : Conclusion (restricted p') (selector d) (beta d) N :=
    actual_finite_conclusion (restricted p') hdSmall hcSmall hnSmall' (selector d) (beta d)
      (selector_sum d) (selector_beta d) hbSmall huSmall N hlarge
  have hbFull : laplacian p' *ᵥ (extend (beta d) : Option (CoreIndex d ⊕ J) → ZMod 2)=0 := by
    apply actual_theta_beta_preserved (fullPrimes F) p' hfix holdbits (extend (beta d)) rfl
      (fun _ => rfl) hbeta
    exact actual_laplacian_transpose_ones p' hd' hp2' hn'
  have haFull : (∑ i : Option (CoreIndex d ⊕ J), extend (selector d) i)=0 := by
    rw [extend_sum,selector_sum]
  have habFull : dotProduct (extend (selector d) : Option (CoreIndex d ⊕ J) → ZMod 2)
      (extend (beta d))=1 := by rw [extend_dot,selector_beta]
  have Cfull : Conclusion p' (extend (selector d)) (extend (beta d)) N :=
    actual_finite_conclusion p' hd' hc' hn' (extend (selector d)) (extend (beta d))
      haFull habFull hbFull hunit' N hlarge
  exact ⟨p',hp',hd',hβfixed,hθfixed,havoid,hfactor,Csmall,Cfull⟩

end ActualTwoDescentSimultaneousProducer318
