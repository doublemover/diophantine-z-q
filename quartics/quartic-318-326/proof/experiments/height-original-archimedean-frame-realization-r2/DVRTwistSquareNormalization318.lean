module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace DVRTwistSquareNormalization318
set_option maxHeartbeats 800000
variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- The normalized local coefficient has uniformizer exponent exactly zero
or one. Its unit and its square multiplier retain the actual input twist. -/
theorem normalize (pi : V) (hp : Irreducible pi) (c : K) (hc : c≠0) :
    ∃ (u : Vˣ) (e : Fin 2) (s : K), s≠0 ∧
      c=algebraMap V K ((u:V)*pi^(e:ℕ))*s^2 := by
  obtain ⟨n,u,hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hp hc
  have hpi : algebraMap V K pi≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective V K).ne hp.ne_zero
  have he0 : 0≤n%2 := Int.emod_nonneg n (by decide)
  have he2 : n%2<2 := Int.emod_lt_of_pos n (by decide)
  let e : Fin 2 := ⟨(n%2).toNat, by omega⟩
  have he : (e:ℤ)=n%2 := Int.toNat_of_nonneg he0
  have hn : n=(e:ℤ)+(n/2)*2 := by omega
  refine ⟨u,e,(algebraMap V K pi)^(n/2),zpow_ne_zero _ hpi,?_⟩
  rw [hu]
  simp only [Units.smul_def,Algebra.smul_def,map_mul,map_pow]
  congr 1
  conv_lhs => rw [hn,zpow_add₀ hpi,zpow_mul]
  simp only [zpow_natCast,zpow_ofNat]

/-- All four original twists are normalized simultaneously, with one
literal equality for each original index and no change in the contact t. -/
theorem normalize_four (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K),
      (∀ i,s i≠0) ∧ ∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2 := by
  have h (i : Fin 4) := normalize V K pi hp (c i:K) (c i).ne_zero
  choose u e s hs hc using h
  exact ⟨u,e,s,hs,hc⟩
end DVRTwistSquareNormalization318
