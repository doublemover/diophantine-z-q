module
public import OriginalSelectedRankFromCorank318
public import ActualTwoDescentParityCorank318
public import OriginalPreparedTwists318
public import ActualTwoDescentPontryaginFreeRankOne318
public import ActualTwoDescentOriginalAllPlacesCardinality318
import all OriginalPreparedTwists318
import all ActualTwoDescentOriginalAllPlacesProducer318
import all ActualTwoDescentMordellWeilControl318
import all ActualTwoDescentActualQuotientControl318
import all ActualTwoDescentOriginalAllPlacesCardinality318
import all ActualTwoDescentSmallPattern318
import all ActualTwoDescentOldCorePreservation318
import all ActualTwoDescentExtendedVectors318
import all ActualTwoDescentPrimeMonomials318
import Lean.Elab.Tactic.Omega
public section
noncomputable section
namespace OriginalSelectedRankFromParity318
open scoped BigOperators
open OriginalPreparedTwists318
open ActualTwoDescentSmallPattern318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentExtendedVectors318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentMordellWeilControl318 ActualTwoDescentOriginalAllPlacesProducer318
open ActualTwoDescentOriginalAllPlacesCardinality318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentAllPlacesExactCardinality318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentSimultaneousLocalClasses318 ActualTwoDescentTorsionKummerValues318
open ActualTwoDescentEllipticModel318 ActualTwoDescentActualShaReducedDuality318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPadicModule318
open OriginalSelectedRankFromCorank318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentParityCorank318
open ActualTwoDescentAdditivePrimaryLevels318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- W is the root-number restriction of the literal curves E_n.
This artifact does not define epsilon factors. The same W is threaded
through the two standard arithmetic suppliers. -/
@[expose] def SelectedRootSign (W : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 0<n → Squarefree n → (n:ZMod 12)=11 → W n = -1

/-- Weak consequence of Dokchitser–Dokchitser 1.8 for the actual
rational 2-isogeny: odd full primary corank implies actual infinitude,
not infinite rational points. No arithmetic Sha hypothesis. -/
@[expose] def OddParitySupplier (W : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, ∀ hp : 0<n, Squarefree n → (n:ZMod 12)=11 → W n = -1 →
    Infinite (actualPrimarySelmer (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne'))

theorem two_reference_slots (n : ℕ) (hr : (n:ZMod 12)=11) :
    n % 24 = 11 ∨ n % 24 = 23 := by
  have hm := (ZMod.natCast_eq_natCast_iff' n 11 12).mp hr
  omega

/-- Exactly two reference signs and the named local-factor comparison
suffice; neither modulo-24 class is imposed as a new selector. -/
theorem sign_from_reference_transport (W : ℕ → ℤ) (r₁₁ : W 11 = -1)
    (r₂₃ : W 23 = -1)
    (cmp : ∀ n r : ℕ, 0<n → Squarefree n → (n:ZMod 12)=11 →
      (r=11 ∨ r=23) → n % 24 = r → W n = W r) :
    SelectedRootSign W := by
  intro n hp hs hr
  rcases two_reference_slots n hr with h | h
  · exact (cmp n 11 hp hs hr (Or.inl rfl) h).trans r₁₁
  · exact (cmp n 23 hp hs hr (Or.inr rfl) h).trans r₂₃

theorem same_native_corank (W : ℕ → ℤ) (sign : SelectedRootSign W)
    (parity : OddParitySupplier W) (n B : ℕ)
    (hp : 0<n) (hs : Squarefree n) (hr : (n:ZMod 12)=11)
    (hcard : AllPlacesEight n) (control : MordellWeilControl n B) :
    NativeCorankOne (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne') := by
  obtain ⟨_,hS⟩ := hcard
  have ht := actual_full_primary_two_card (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne')
    control.1.2.1 control.1.2.2.1 hS
  exact native_free_of_infinite (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne') ht
    (parity n hp hs hr (sign n hp hs hr))

theorem selected_infinite_of_parity (W : ℕ → ℤ) (sign : SelectedRootSign W)
    (parity : OddParitySupplier W) (rank : SourceRankOnly)
    (n B : ℕ) (hp : 0<n) (hs : Squarefree n) (hr : (n:ZMod 12)=11)
    (hcard : AllPlacesEight n) (control : MordellWeilControl n B) :
    Infinite (Point (n:ℚ)) :=
  rank n hp hs hr (same_native_corank W sign parity n B hp hs hr hcard control)

private theorem allPlacesEight_of_marked {U : Type} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (a bits : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a bits N)
    (i₀ i₁ : Option U) (h₀ : bits i₀=0) (h₁ : bits i₁=1)
    (B : ℕ) (hmono : monomial p bits=B) (hlocal : AllPlacesBeta (∏ i, p i) B) :
    AllPlacesEight (∏ i, p i) := by
  subst B
  obtain ⟨hn,hb,hmem⟩ := hlocal
  have hcop := actual_conclusion_coprime p a bits N C
  have hp₂ : ∀ i, p i≠2 := by
    intro i he
    have h := hcop i
    rw [he] at h
    norm_num at h
  have hp₃ : ∀ i, p i≠3 := by
    intro i he
    have h := hcop i
    rw [he] at h
    norm_num at h
  exact ⟨hn,actual_all_places_card_eight p hinj hp₂ hp₃ a bits N C i₀ i₁ h₀ h₁ hn hmem⟩

/-- Discharge the exact old paired rank gate without reselecting either
twist or strengthening beta. The genuine all-place count comes from the
marked membership and finite local constraints, not SignedActualSpace. -/
theorem paired_of_parity (W : ℕ → ℤ) (sign : SelectedRootSign W)
    (parity : OddParitySupplier W) (rank : SourceRankOnly) : RestrictedRC := by
  intro d J _ _ qB qJ p hp N hinj hB hJ hfactor Csmall Cfull _ MWfull MWsmall Lfull Lsmall
  classical
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  letI : ∀ i : Index d, Fact (restricted p i).Prime := fun i => ⟨hp (oldEmbedding i)⟩
  have hemb : Function.Injective (oldEmbedding : Index d → Option (CoreIndex d ⊕ J)) := by
    intro i j he
    cases i <;> cases j <;> simp_all [oldEmbedding]
  have hmonoSmall : monomial (restricted p) (beta d)=∏ i, qB i := by
    calc
      _ = ∏ i : BetaIndex d, restricted p (bIndex i) := by
        simp [monomial,Fintype.prod_option,Fintype.prod_sum_type,beta,bIndex]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        exact hB i
  have hmonoFull : monomial p (extend (beta d))=∏ i, qB i := by
    rw [actual_extended_monomial,hmonoSmall]
  have ES := allPlacesEight_of_marked (restricted p) (hinj.comp hemb)
    (selector d) (beta d) N Csmall none (bIndex none) rfl rfl _ hmonoSmall Lsmall
  have EF := allPlacesEight_of_marked p hinj (extend (selector d)) (extend (beta d))
    N Cfull none (some (Sum.inl (Sum.inl none))) rfl rfl _ hmonoFull Lfull
  exact ⟨selected_infinite_of_parity W sign parity rank _ _ (lt_of_le_of_lt (Nat.zero_le N) Csmall.large)
      Csmall.squarefree Csmall.residue ES MWsmall,
    selected_infinite_of_parity W sign parity rank _ _ (lt_of_le_of_lt (Nat.zero_le N) Cfull.large)
      Cfull.squarefree Cfull.residue EF MWfull⟩

end OriginalSelectedRankFromParity318

#print axioms OriginalSelectedRankFromParity318.same_native_corank
#print axioms OriginalSelectedRankFromParity318.paired_of_parity
