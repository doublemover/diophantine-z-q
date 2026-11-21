module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualFTRayIndexTwo318

variable {A G : Type*} [CommGroup A] [Group G]

/-- An injective index-two relative Artin image, with the actual
nontrivial rational branch represented by j. No class-cardinality or
rational-conjugacy conclusion is an input. σ will be literal Gaussian
conjugation, not an independently chosen involution. -/
structure Presentation (σ : A →* A) where
  incl : A →* G
  inj : Function.Injective incl
  j : G
  outside : ∀ x : A, incl x ≠ j
  cover : ∀ g : G, ∃ x : A, g = incl x ∨ g = incl x * j
  conjugates : ∀ x : A, j * incl x * j⁻¹ = incl (σ x)

namespace Presentation

variable {σ : A →* A} (P : Presentation (G := G) σ)

@[expose] def atBranch (x : A × Bool) : G :=
  if x.2 then P.incl x.1 * P.j else P.incl x.1

theorem atBranch_injective : Function.Injective P.atBranch := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases b <;> cases d
  · change P.incl a = P.incl c at h
    rw [P.inj h]
  · change P.incl a = P.incl c * P.j at h
    exfalso
    apply P.outside (c⁻¹ * a)
    rw [map_mul,map_inv,h]
    group
  · change P.incl a * P.j = P.incl c at h
    exfalso
    apply P.outside (a⁻¹ * c)
    rw [map_mul,map_inv,←h]
    group
  · change P.incl a * P.j = P.incl c * P.j at h
    rw [P.inj (mul_right_cancel h)]

theorem atBranch_surjective : Function.Surjective P.atBranch := by
  intro g
  obtain ⟨a,h|h⟩ := P.cover g
  · exact ⟨(a,false),h.symm⟩
  · exact ⟨(a,true),h.symm⟩

/-- Rational degree is computed from the two actual Gaussian branches. -/
def equiv : (A × Bool) ≃ G :=
  Equiv.ofBijective P.atBranch ⟨P.atBranch_injective,P.atBranch_surjective⟩

include P in
theorem card [Finite A] : Nat.card G = 2 * Nat.card A := by
  rw [←Nat.card_congr P.equiv,Nat.card_prod]
  have h : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card] <;> decide
  rw [h,mul_comm]

/-- Rational conjugacy has exactly the literal relative class and the
one fixed conjugated class. Neither direction needs Chebotarev. -/
theorem conjugate_iff (a : A) (g : G) :
    (∃ t : G, t * P.incl a * t⁻¹ = g) ↔
    g = P.incl a ∨ g = P.incl (σ a) := by
  have abel (u b : A) : P.incl u * P.incl b * (P.incl u)⁻¹ = P.incl b := by
    calc
      _ = P.incl ((u*b)*u⁻¹) := by
        rw [map_mul P.incl (u*b) u⁻¹,map_mul P.incl u b,map_inv]
      _ = P.incl b := congrArg P.incl (by rw [mul_comm u b,mul_assoc,mul_inv_cancel,mul_one])
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨u,h|h⟩ := P.cover t
    · rw [h] at ht
      exact Or.inl (ht.symm.trans (abel u a))
    · right
      calc
        g = t * P.incl a * t⁻¹ := ht.symm
        _ = P.incl u * (P.j * P.incl a * P.j⁻¹) * (P.incl u)⁻¹ := by rw [h]; group
        _ = P.incl (σ a) := by rw [P.conjugates,abel]
  · rintro (rfl|rfl)
    · exact ⟨1,by simp⟩
    · exact ⟨P.j,P.conjugates a⟩

/-- Checking compatibility on the arithmetic Artin image and complex
conjugation uniquely determines the rational cyclotomic restriction. -/
theorem hom_ext {K : Type*} [Monoid K] (c d : G →* K)
    (hA : ∀ a, c (P.incl a) = d (P.incl a))
    (hj : c P.j = d P.j) : c = d := by
  ext t
  obtain ⟨a,h|h⟩ := P.cover t
  · simpa only [h] using hA a
  · rw [h,map_mul,map_mul,hA,hj]

end Presentation

end ActualFTRayIndexTwo318
