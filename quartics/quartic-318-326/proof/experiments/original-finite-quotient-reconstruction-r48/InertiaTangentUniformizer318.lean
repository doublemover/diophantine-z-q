module
public import DVRInertiaCharacterParity318
public section
noncomputable section
namespace InertiaTangentUniformizer318
open IsLocalRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]

/-- The actual anti-invariant element, without dividing by an unchosen half. -/
@[expose] def anti (τ : R ≃+* R) (p : R) : R := p - τ p

/-- A genuine order2 automorphism with tangent action -1 admits an actual
anti-invariant uniformizer. The congruence is in the ORIGINAL local ring,
not in a replacement power-series model. -/
theorem anti_uniformizer (τ : R ≃+* R) (hτ : ∀ x, τ (τ x) = x)
    (p : R) (hp : Irreducible p) (htangent : p ^ 2 ∣ τ p + p) :
    Irreducible (anti τ p) ∧ τ (anti τ p) = -anti τ p := by
  obtain ⟨a, ha⟩ := htangent
  have hp0 : residue R p = 0 := by
    by_contra h
    exact hp.not_isUnit ((residue_ne_zero_iff_isUnit p).mp h)
  have hfactor : anti τ p = (2 - p * a) * p := by
    dsimp only [anti]
    linear_combination -ha
  have hu : IsUnit (2 - p * a) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa only [map_sub, map_ofNat, map_mul, hp0, zero_mul, sub_zero] using
      (show (2 : ResidueField R) ≠ 0 by norm_num)
  obtain ⟨u, hu⟩ := hu
  have hassoc : Associated p (anti τ p) := by
    refine ⟨u, ?_⟩
    rw [hu, hfactor] <;> ring
  refine ⟨hassoc.irreducible hp, ?_⟩
  dsimp only [anti]
  rw [map_sub, hτ] <;> ring
end InertiaTangentUniformizer318
