module
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ActualPrimitiveOrderGeneration318
open Polynomial
variable (C R A : Type*) [CommRing C] [CommRing R] [CommRing A]
  [Algebra C R] [Algebra C A]
variable (f : R →ₐ[C] A) (d : R)

/-- Actual polynomial expressions for every member of a FULL original
finite algebra generating set imply surjectivity onto the ENTIRE literal
source localization. The inverse base denominator is included explicitly;
no fraction-field equality is substituted for an order equality. -/
theorem polynomial_surjective
    (s : Finset A) (hs : Algebra.adjoin C (s : Set A) = ⊤)
    (β : Localization.Away (f d))
    (hg : ∀ a ∈ s, ∃ P : Polynomial (Localization.Away d),
      P.eval₂ (Localization.awayMap f.toRingHom d) β =
        algebraMap A (Localization.Away (f d)) a) :
    Function.Surjective
      (Polynomial.eval₂RingHom (Localization.awayMap f.toRingHom d) β) := by
  let B := Localization.Away d
  let L := Localization.Away (f d)
  let g : B →+* L := Localization.awayMap f.toRingHom d
  let E : Polynomial B →+* L := Polynomial.eval₂RingHom g β
  have hg0 (a : R) : g (algebraMap R B a) = algebraMap A L (f a) := by
    simp only [B, L, g, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  let T : Subalgebra C L := {
    carrier := Set.range E
    zero_mem' := ⟨0, map_zero E⟩
    one_mem' := ⟨1, map_one E⟩
    add_mem' := by
      rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p + q, map_add E p q⟩
    mul_mem' := by
      rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p * q, map_mul E p q⟩
    algebraMap_mem' := by
      intro c
      refine ⟨Polynomial.C (algebraMap R B (algebraMap C R c)), ?_⟩
      change Polynomial.eval₂ g β (Polynomial.C _) = _
      rw [Polynomial.eval₂_C, hg0, f.commutes,
        ← IsScalarTower.algebraMap_apply C A L] }
  have hle : Algebra.adjoin C (s : Set A) ≤
      T.comap (IsScalarTower.toAlgHom C A L) := by
    apply Algebra.adjoin_le
    intro a ha
    exact hg a ha
  have hA (a : A) : algebraMap A L a ∈ T := by
    apply hle
    rw [hs]
    trivial
  have hB (b : B) : g b ∈ T :=
    ⟨Polynomial.C b, Polynomial.eval₂_C g β⟩
  let c : B := IsLocalization.Away.invSelf d
  have hc : algebraMap R B d * c = 1 := IsLocalization.Away.mul_invSelf d
  have hcL : algebraMap A L (f d) * g c = 1 := by
    rw [← hg0, ← map_mul, hc, map_one]
  intro z
  obtain ⟨⟨a, t, ht⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (f d)) z
  obtain ⟨n, rfl⟩ := ht
  have hz' : z * (algebraMap A L (f d)) ^ n = algebraMap A L a := by
    simpa only [L, map_pow] using hz
  have he : z = algebraMap A L a * (g c) ^ n := by
    rw [← hz', mul_assoc, ← mul_pow, hcL, one_pow, mul_one]
  have hm : z ∈ T := by
    rw [he]
    exact T.mul_mem (hA a) (T.pow_mem (hB c) n)
  exact hm
end ActualPrimitiveOrderGeneration318
