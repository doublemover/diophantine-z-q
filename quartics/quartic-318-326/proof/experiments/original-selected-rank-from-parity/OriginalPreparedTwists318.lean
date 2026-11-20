module
public import OriginalJoinedPrimeSource318
public import ActualTwoDescentOriginalAllPlacesProducer318
import all OriginalJoinedPrimeSource318
public section
noncomputable section
namespace OriginalPreparedTwists318
open scoped BigOperators
open ActualTwoDescentSmallPattern318 ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open ActualTwoDescentFiniteConclusion318 ActualTwoDescentMordellWeilControl318
open ActualTwoDescentOriginalAllPlacesProducer318 ActualTwoDescentEllipticModel318
open ActualTwoDescentPointExtraction318 TwoTwistPointRealization318
open ActualTwoDescentSignedActualCardinality318 ActualTwoDescentSimultaneousProducer318
open OriginalJoinedPrimeSource318

/-- Arithmetic squareclass extraction at the ACTUAL pole. The empty theta
support is legal. The two Jacobi conditions concern products, not pairwise
residuacity of the individual support primes. -/
structure Eligible (b : ℚ) where
  size : ℕ
  J : Type
  jf : Fintype J
  jd : DecidableEq J
  qB : BetaIndex size → ℕ
  qJ : J → ℕ
  primeB : ∀ i, (qB i).Prime
  primeJ : ∀ j, (qJ j).Prime
  injectiveB : Function.Injective qB
  injectiveJ : Function.Injective qJ
  disjoint : ∀ i j, qB i ≠ qJ j
  beta24 : ((∏ i, qB i : ℕ) : ZMod 24)=17
  theta24 : letI := jf; ((∏ j, qJ j : ℕ) : ZMod 24)=1
  symbols : letI := jf; MutualSymbols qB qJ
  c e : ℚ
  c_ne : c≠0
  e_ne : e≠0
  first_class : 17*b=((∏ i, qB i : ℕ):ℚ)*c^2
  second_class : letI := jf; 1-b/17=((∏ j, qJ j : ℕ):ℚ)*e^2

def Eligibility : Prop := ∀ b : ℚ, Ready b → Nonempty (Eligible b)

/-- No generic BSD or rank implication. This explicit boundary is asked only
on the TWO concrete retained finite-descent packages, with original beta,
actual all-place membership, cardinal eight and Mordell--Weil control.
Infinitude is enough because native control produces the marked Kummer point. -/
def RestrictedRC : Prop :=
  ∀ (d : ℕ) {J : Type} [Fintype J] [DecidableEq J]
    (qB : BetaIndex d → ℕ) (qJ : J → ℕ)
    (p : Option (CoreIndex d ⊕ J) → ℕ) (hp : ∀ i, (p i).Prime)
    (N : ℕ),
    Function.Injective p →
    (∀ i, p (some (Sum.inl (Sum.inl i)))=qB i) →
    (∀ j, p (some (Sum.inr j))=qJ j) →
    (∏ i, p i)=(∏ i, restricted p i)*(∏ j, qJ j) →
    Conclusion (restricted p) (selector d) (beta d) N →
    Conclusion p (extend (selector d)) (extend (beta d)) N →
    (letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
     letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
     Nat.card (SignedActualSpace p)=8 ∧ Nat.card (SignedActualSpace (restricted p))=8) →
    MordellWeilControl (∏ i, p i) (∏ i, qB i) →
    MordellWeilControl (∏ i, restricted p i) (∏ i, qB i) →
    AllPlacesBeta (∏ i, p i) (∏ i, qB i) →
    AllPlacesBeta (∏ i, restricted p i) (∏ i, qB i) →
    Infinite (Point ((∏ i, restricted p i : ℕ):ℚ)) ∧
      Infinite (Point ((∏ i, p i : ℕ):ℚ))

/-- Native finite and local producers are unconditional at their own boundaries.
This construction invokes RC only after actual paired twists are selected. -/
theorem literal_points {b : ℚ} (B : Eligible b) (hb : b≠0) (rc : RestrictedRC)
    (forbidden : Finset ℕ) (N : ℕ) : Nonempty (NormalizedPolePoints318.PointPair b) := by
  letI : Fintype B.J := B.jf
  letI : DecidableEq B.J := B.jd
  letI : ∀ i, Fact (B.qB i).Prime := fun i => ⟨B.primeB i⟩
  letI : ∀ j, Fact (B.qJ j).Prime := fun i => ⟨B.primeJ i⟩
  obtain ⟨p,hp,hinj,hB,hJ,_,hfac,Csmall,Cfull,hcard,MWfull,MWsmall,Lfull,Lsmall⟩ :=
    actual_simultaneous_all_places B.size B.qB B.qJ B.injectiveB B.injectiveJ
      B.disjoint B.beta24 B.theta24 B.symbols forbidden N
  obtain ⟨hsmall,hfull⟩ := rc B.size B.qB B.qJ p hp N hinj
    hB hJ hfac Csmall Cfull hcard MWfull MWsmall Lfull Lsmall
  obtain ⟨P⟩ := MWsmall.2.2.2.2 hsmall
  obtain ⟨R⟩ := MWfull.2.2.2.2 hfull
  let β : ℚ := ((∏ i, B.qB i : ℕ):ℚ)
  let θ : ℚ := ((∏ i, B.qJ i : ℕ):ℚ)
  let n : ℚ := ((∏ i, restricted p i : ℕ):ℚ)
  have hβ : β≠0 := by
    dsimp [β]
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr (fun i _ => (B.primeB i).ne_zero))
  have h17 : (17*b:ℚ)≠0 := mul_ne_zero (by norm_num) hb
  have hV : (17*b)^2*(1-b/17)=θ*((17*b)*B.e)^2 := by
    rw [B.second_class]
    dsimp [θ]
    ring
  have htwist : ((∏ i, p i : ℕ):ℚ)=n*θ := by
    dsimp [n,θ]
    exact_mod_cast hfac
  have Q : KummerPoint β (n*θ) := by
    rw [←htwist]
    exact R
  exact ⟨(actual_realization_of_kummer b β θ B.c ((17*b)*B.e) n hβ
    B.c_ne (mul_ne_zero h17 B.e_ne) B.first_class hV P Q).pointPair⟩

theorem points_of_prepared (eligible : Eligibility) (rc : RestrictedRC)
    (b : ℚ) (hb : Ready b) : Nonempty (NormalizedPolePoints318.PointPair b) := by
  obtain ⟨B⟩ := eligible b hb
  exact literal_points B hb.1.ne' rc ∅ 0

end OriginalPreparedTwists318
