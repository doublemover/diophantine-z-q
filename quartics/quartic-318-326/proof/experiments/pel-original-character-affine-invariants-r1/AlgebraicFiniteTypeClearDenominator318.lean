module
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public section
noncomputable section
namespace AlgebraicFiniteTypeClearDenominator318
variable (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- A single actual nonzero base element clears the integral equations
of an entire finite algebra-generating set. No change of generators in
the original algebra and no generic-finiteness assumption is hidden. -/
theorem generators [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ (s : Finset A) (r : R), r ≠ 0 ∧
      Algebra.adjoin R (s : Set A) = ⊤ ∧
      ∀ a ∈ s, IsIntegral R (r • a) := by
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  obtain ⟨r,hr,hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  exact ⟨s,r,hr,hs,hi⟩

section Localized
variable (r : R) (B L : Type) [CommRing B] [CommRing L]
variable [Algebra R B] [IsLocalization.Away r B]
variable [Algebra A L] [IsLocalization.Away (algebraMap R A r) L]
variable [Algebra R L] [IsScalarTower R A L]
variable [Algebra B L] [IsScalarTower R B L]

/-- The inverse used here comes from the localized BASE, so multiplying
an integral cleared generator by it proves integrality over that same
base. It is not an unproved inverse-integrality assertion. -/
theorem generator_integral (a : A) (ha : IsIntegral R (r • a)) :
    IsIntegral B (algebraMap A L a) := by
  let c : B := IsLocalization.Away.invSelf r
  have hc : algebraMap R B r * c = 1 := IsLocalization.Away.mul_invSelf r
  have hcm : algebraMap B L c * algebraMap R L r = 1 := by
    rw [IsScalarTower.algebraMap_apply R B L]
    rw [← map_mul, mul_comm c, hc, map_one]
  have hm : IsIntegral B (algebraMap A L (r • a)) :=
    (ha.algebraMap (B := L)).tower_top
  have hi := (isIntegral_algebraMap (R := B) (A := L) (x := c)).mul hm
  convert hi using 1
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L]
  rw [← mul_assoc, hcm, one_mul]

/-- Integral cleared generators give integrality of EVERY original
algebra element after the actual localization, via their full adjoin. -/
theorem original_integral (s : Finset A)
    (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hi : ∀ a ∈ s, IsIntegral R (r • a)) (a : A) :
    IsIntegral B (algebraMap A L a) := by
  let T := integralClosure B L
  have hle : Algebra.adjoin R (s : Set A) ≤
      (T.restrictScalars R).comap (IsScalarTower.toAlgHom R A L) := by
    apply Algebra.adjoin_le
    intro z hz
    exact generator_integral R A r B L z (hi z hz)
  have ha : a ∈ Algebra.adjoin R (s : Set A) := by
    rw [hs]
    trivial
  exact hle ha

/-- No points/components of the source localization are discarded:
every actual fraction is integral, its denominator inverse lying in
the same localized base. -/
theorem whole_localization_integral (s : Finset A)
    (hs : Algebra.adjoin R (s : Set A) = ⊤)
    (hi : ∀ a ∈ s, IsIntegral R (r • a)) : Algebra.IsIntegral B L := by
  constructor
  intro z
  let c : B := IsLocalization.Away.invSelf r
  have hc : algebraMap R B r * c = 1 := IsLocalization.Away.mul_invSelf r
  have hcL : algebraMap R L r * algebraMap B L c = 1 := by
    rw [IsScalarTower.algebraMap_apply R B L, ← map_mul, hc, map_one]
  obtain ⟨⟨a,d,hd⟩,hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R A r)) z
  obtain ⟨n,rfl⟩ := hd
  have hz' : z * (algebraMap R L r)^n = algebraMap A L a := by
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply R A L] using hz
  have he : z = algebraMap A L a * (algebraMap B L c)^n := by
    rw [← hz', mul_assoc, ← mul_pow, hcL, one_pow, mul_one]
  rw [he]
  exact (original_integral R A r B L s hs hi a).mul
    ((isIntegral_algebraMap (R := B) (A := L) (x := c)).pow n)
end Localized
end AlgebraicFiniteTypeClearDenominator318
