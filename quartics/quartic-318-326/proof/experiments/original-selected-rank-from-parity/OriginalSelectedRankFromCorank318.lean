module
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
public section
noncomputable section
namespace OriginalSelectedRankFromCorank318
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
open ActualTwoDescentPontryaginFreeRankOne318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Rank of the native Pontryagin dual of the genuine discrete full
2-primary Selmer group, not rank of a signed comparison space. -/
@[expose] def NativeCorankOne (n : ℚ) (hn : n≠0) : Prop :=
  letI := actualPontryaginPadicModule n hn
  Nonempty (Additive (ActualPontryagin n hn) ≃ₗ[ℤ_[2]] ℤ_[2])

/-- Classical supplier: precisely the alternating nondegenerate pairing
on the actual REDUCED 2-primary Sha quotient of a queried selected twist. -/
@[expose] def ReducedPairingSupplier : Prop :=
  ∀ n : ℕ, ∀ hp : 0<n, Squarefree n → (n:ZMod 12)=11 →
    Nat.card (allPlacesImage (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne'))=8 →
    ActualReducedDuality (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne')

/-- Restricted rank-only statement left by the source 2-converse and
analytic-rank-one to MW implication. No finite Sha or new twist choice. -/
@[expose] def SourceRankOnly : Prop :=
  ∀ n : ℕ, ∀ hp : 0<n, Squarefree n → (n:ZMod 12)=11 →
    NativeCorankOne (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne') →
    Infinite (Point (n:ℚ))

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

theorem selected_infinite (pairing : ReducedPairingSupplier) (rank : SourceRankOnly)
    (n B : ℕ) (hp : 0<n) (hs : Squarefree n) (hr : (n:ZMod 12)=11)
    (hcard : AllPlacesEight n) (control : MordellWeilControl n B) :
    Infinite (Point (n:ℚ)) := by
  obtain ⟨_,hS⟩ := hcard
  apply rank n hp hs hr
  exact actual_native_pontryagin_free_rank_one (n:ℚ) (Nat.cast_ne_zero.mpr hp.ne')
    control.1.2.1 control.1.2.2.1 hS (pairing n hp hs hr hS)

/-- Discharge the exact old paired rank gate without reselecting either
twist or strengthening beta. The genuine all-place count comes from the
marked membership and finite local constraints, not SignedActualSpace. -/
theorem paired (pairing : ReducedPairingSupplier) (rank : SourceRankOnly) : RestrictedRC := by
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
  exact ⟨selected_infinite pairing rank _ _ (lt_of_le_of_lt (Nat.zero_le N) Csmall.large)
      Csmall.squarefree Csmall.residue ES MWsmall,
    selected_infinite pairing rank _ _ (lt_of_le_of_lt (Nat.zero_le N) Cfull.large)
      Cfull.squarefree Cfull.residue EF MWfull⟩

end OriginalSelectedRankFromCorank318
