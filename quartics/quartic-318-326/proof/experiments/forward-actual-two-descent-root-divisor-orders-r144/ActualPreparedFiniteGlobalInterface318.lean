module
public import ActualPreparedPrimeSupport318
public import ActualPreparedPoleSquarefreeClasses318
public import ActualTwoDescentOriginalMordellWeilProducer318
public section
noncomputable section
namespace ActualPreparedFiniteGlobalInterface318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPrimeSupport318
open ActualPreparedMutualSymbolConversion318 ActualTwoDescentOriginalMordellWeilProducer318
open ActualTwoDescentMordellWeilControl318 ActualTwoDescentEllipticModel318
open ActualTwoDescentPointExtraction318
open ActualTwoDescentOldCorePreservation318 TwoTwistPointRealization318
open scoped BigOperators

/-- Exact finite descent at the fixed actual pole. Positive squarefree class
representatives, their residue laws, coprimality and both local root families
are consumed literally. The simultaneous prime arrays are CONSTRUCTED from
those coefficients. Rational-group infinitude is not inferred: the final
point extraction retains it on BOTH constructed twists. -/
theorem from_classes {b : ℚ} (C : Classes b)
    (hBeta24 : (C.beta:ZMod 24)=17) (hTheta24 : (C.theta:ZMod 24)=1)
    (hcop : Nat.Coprime C.beta C.theta)
    (hTheta : ∀ (p : ℕ) [Fact p.Prime], p∣C.beta →
      ∃ r : ℚ_[p], r^2=(C.theta:ℚ_[p]))
    (hBeta : ∀ (p : ℕ) [Fact p.Prime], p∣C.theta →
      ∃ r : ℚ_[p], r^2=(C.beta:ℚ_[p])) (N : ℕ) :
    ∃ n : ℕ, N<n ∧ Squarefree n ∧ Squarefree (n*C.theta) ∧
      (n:ZMod 12)=11 ∧ (n*C.theta:ZMod 12)=11 ∧
      MordellWeilControl n C.beta ∧ MordellWeilControl (n*C.theta) C.beta ∧
      (Infinite (Point (n:ℚ)) → Infinite (Point ((n*C.theta:ℕ):ℚ)) →
        Nonempty (Realization b)) := by
  classical
  have hb1 : C.beta≠1 := by
    intro he
    rw [he] at hBeta24
    norm_num at hBeta24
  have hbgt : 1<C.beta := by have := C.beta_pos; omega
  obtain ⟨d,qB,hBp,hBi,hBfac,hBd⟩ := beta_support C.beta C.beta_squarefree hbgt
  let J := ↥C.theta.primeFactors
  let qJ : J → ℕ := fun j => j.val
  have hJp : ∀ j, (qJ j).Prime := fun j => Nat.prime_of_mem_primeFactors j.property
  have hJi : Function.Injective qJ := fun _ _ h => Subtype.ext h
  have hJd : ∀ j, qJ j∣C.theta := fun j => Nat.dvd_of_mem_primeFactors j.property
  have hJfac : (∏ j, qJ j)=C.theta := prime_support_product C.theta C.theta_squarefree
  letI : ∀ i, Fact (qB i).Prime := fun i => ⟨hBp i⟩
  letI : ∀ j, Fact (qJ j).Prime := fun j => ⟨hJp j⟩
  have hdis := support_disjoint C.beta C.theta qB qJ hBp hBd hJd hcop
  have hmutual := mutual_symbols_of_coefficient_roots C.beta C.theta qB qJ
    hBfac hJfac hdis hTheta hBeta
  obtain ⟨p,hp,hpi,hBfix,hJfix,havoid,hfactor,Csmall,Cfull,hcards,Hfull,Hsmall⟩ :=
    actual_simultaneous_mordell_weil d qB qJ hBi hJi hdis
      (by simpa only [hBfac] using hBeta24)
      (by simpa only [hJfac] using hTheta24) hmutual ∅ N
  let n : ℕ := ∏ i, restricted p i
  have hfull : (∏ i, p i)=n*C.theta := by
    simpa only [hJfac] using hfactor
  have Hn : MordellWeilControl n C.beta := by
    simpa only [hBfac] using Hsmall
  have Hnt : MordellWeilControl (n*C.theta) C.beta := by
    simpa only [hfull,hBfac] using Hfull
  refine ⟨n,Csmall.large,Csmall.squarefree,?_,Csmall.residue,?_,Hn,Hnt,?_⟩
  · simpa only [hfull] using Cfull.squarefree
  · simpa only [hfull,Nat.cast_mul] using Cfull.residue
  · intro hinf hinft
    obtain ⟨P⟩ := Hn.2.2.2.2 hinf
    obtain ⟨Q⟩ := Hnt.2.2.2.2 hinft
    have Q' : KummerPoint (C.beta:ℚ) ((n:ℚ)*(C.theta:ℚ)) := by
      simpa only [Nat.cast_mul] using Q
    exact ⟨actual_realization_of_kummer b C.beta C.theta C.c C.d n
      (by exact_mod_cast (Nat.ne_of_gt C.beta_pos)) C.c_ne C.d_ne
      C.first_class C.second_class P Q'⟩

end ActualPreparedFiniteGlobalInterface318
