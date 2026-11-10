module
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Basic
public section
noncomputable section
namespace RegularPrincipalIdealFrame318
universe u
variable (A : Type u) [CommRing A] (c : A)
  (hc : ∀ a : A,a*c=0 → a=0)

/-- Multiplication by the actual regular equation into its ACTUAL ideal.
Its inclusion into A, not merely its abstract rank, is retained. -/
@[expose] def multiply : A →ₗ[A] Ideal.span ({c} : Set A) where
  toFun a := ⟨a*c,Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩⟩
  map_add' a b := Subtype.ext (add_mul a b c)
  map_smul' a b := Subtype.ext (mul_assoc a b c)

lemma multiply_bijective : Function.Bijective (multiply A c) := by
  constructor
  · intro a b hab
    have h : (a-b)*c=0 := by
      rw [sub_mul]
      exact sub_eq_zero.mpr (congrArg Subtype.val hab)
    exact sub_eq_zero.mp (hc (a-b) h)
  · intro x
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp x.property
    exact ⟨a,Subtype.ext ha⟩

/-- The literal zero ideal is an invertible rank-one module on this
chart, with the actual multiplication inclusion fixed. -/
@[expose] def equivalence : A ≃ₗ[A] Ideal.span ({c} : Set A) :=
  LinearEquiv.ofBijective (multiply A c) (multiply_bijective A c hc)

lemma equivalence_value (a : A) : (equivalence A c hc a).val=a*c := rfl
end RegularPrincipalIdealFrame318
