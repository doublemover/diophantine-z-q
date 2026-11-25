module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public section
noncomputable section

namespace OriginalR8WildFixedIntegralOrder318

universe u v w z
variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {L : Type v} [Field L] [Algebra A L] [IsFractionRing A L]
variable {M : Type w} [Field M] [Algebra L M] [Algebra A M] [IsScalarTower A L M]
variable {B : Type z} [CommRing B] [Algebra A B] [Algebra B M] [IsScalarTower A B M]
variable [IsIntegralClosure B A M]

/-- Finite generic diamond/frame invariants on the same field give the
actual whole arithmetic order, not just a suborder with the same χ.
No averaging or inversion of any order of a stabilizer occurs. -/
theorem fixed_order {G : Type*} (σ : G → M ≃ₐ[L] M)
    (generic_fixed : ∀ m : M, (∀ g : G, σ g m = m) →
      ∃ t : L, algebraMap L M t = m) (b : B) :
    (∀ g : G, σ g (algebraMap B M b) = algebraMap B M b) ↔
      ∃ a : A, algebraMap A B a = b := by
  constructor
  · intro hb
    obtain ⟨t, ht⟩ := generic_fixed (algebraMap B M b) hb
    have hM : IsIntegral A (algebraMap B M b) := by
      exact (IsIntegralClosure.isIntegral_iff (A := B)).mpr ⟨b,rfl⟩
    have htInt : IsIntegral A t := by
      apply (isIntegral_algebraMap_iff (B := M)).mp
      exact ht.symm ▸ hM
    obtain ⟨a,ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp htInt
    refine ⟨a,IsIntegralClosure.algebraMap_injective B A M ?_⟩
    calc
      algebraMap B M (algebraMap A B a) = algebraMap A M a :=
        (IsScalarTower.algebraMap_apply A B M a).symm
      _ = algebraMap L M (algebraMap A L a) := IsScalarTower.algebraMap_apply A L M a
      _ = algebraMap L M t := congrArg (algebraMap L M) ha
      _ = algebraMap B M b := ht
  · rintro ⟨a,rfl⟩ g
    rw [← IsScalarTower.algebraMap_apply A B M a, IsScalarTower.algebraMap_apply A L M a]
    exact (σ g).commutes (algebraMap A L a)

end OriginalR8WildFixedIntegralOrder318

#print axioms OriginalR8WildFixedIntegralOrder318.fixed_order
