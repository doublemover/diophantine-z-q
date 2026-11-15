module
public import DVRTwistSquareNormalization318
public import IntegralValuativeRootCoordinates318
public section
noncomputable section
namespace DVRNormalizedContactPoint318
set_option maxHeartbeats 800000
section Field
variable {K : Type*} [Field K]

/-- The normalized root is the original signed root divided by the exact
square multiplier, including when the original root is zero at a contact. -/
theorem root_relation (c d s a t y : K) (hs : s≠0)
    (hc : c=d*s^2) (hy : y^2=c*(t-a)) :
    (y/s)^2=d*(t-a) := by
  rw [div_pow,hy,hc]
  field_simp [hs]
  <;> ring

/-- Scaling back recovers the original root itself, not only its square. -/
theorem original_root (s y : K) (hs : s≠0) : s*(y/s)=y := by
  field_simp [hs]

end Field

variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]

/-- At an integral original t, all four locally normalized signed roots
are integral even when a normalized twist contains the uniformizer. This
includes excluded twist primes; no unit-twist hypothesis is introduced. -/
theorem integral_roots (pi : V) (hp : Irreducible pi) (c : Fin 4 → Kˣ)
    (a : Fin 4 → V) (t : V) (y : Fin 4 → K)
    (hy : ∀ i,(y i)^2=(c i:K)*(algebraMap V K t-algebraMap V K (a i))) :
    ∃ (u : Fin 4 → Vˣ) (e : Fin 4 → Fin 2) (s : Fin 4 → K) (z : Fin 4 → V),
      (∀ i,s i≠0) ∧
      (∀ i,(c i:K)=algebraMap V K ((u i:V)*pi^(e i:ℕ))*(s i)^2) ∧
      (∀ i,algebraMap V K (z i)=y i/s i) ∧
      (∀ i,(z i)^2=((u i:V)*pi^(e i:ℕ))*(t-a i)) ∧
      (∀ i,s i*algebraMap V K (z i)=y i) := by
  obtain ⟨u,e,s,hs,hc⟩ := DVRTwistSquareNormalization318.normalize_four V K pi hp c
  have h (i : Fin 4) : ∃ z : V, algebraMap V K z=y i/s i ∧
      z^2=((u i:V)*pi^(e i:ℕ))*(t-a i) := by
    apply IntegralValuativeRootCoordinates318.square_preimage V K
    rw [map_mul,map_sub]
    exact root_relation _ _ _ _ _ _ (hs i) (hc i) (hy i)
  choose z hz hz2 using h
  refine ⟨u,e,s,z,hs,hc,hz,hz2,?_⟩
  intro i
  rw [hz]
  exact original_root _ _ (hs i)
end DVRNormalizedContactPoint318
