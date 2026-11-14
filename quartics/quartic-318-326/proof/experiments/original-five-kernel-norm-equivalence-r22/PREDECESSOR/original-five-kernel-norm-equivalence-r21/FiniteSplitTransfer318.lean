module
public import SplitAdditiveRetraction318
public import Mathlib.LinearAlgebra.Pi

public section
noncomputable section
namespace FiniteSplitTransfer318
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {S : Type*} [AddCommGroup S]
variable {T : I → Type*} [∀ i, AddCommGroup (T i)]
variable (p : ∀ i, T i →+ S) (t : ∀ i, S →+ T i)

@[expose] def sumPullback : ((i : I) → T i) →+ S where
  toFun y := ∑ i, p i (y i)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

@[expose] def allTransfers : S →+ ((i : I) → T i) where
  toFun x i := t i x
  map_zero' := by ext i; exact (t i).map_zero
  map_add' x y := by ext i; exact (t i).map_add x y

theorem sumPullback_apply (y : (i : I) → T i) : sumPullback p y = ∑ i, p i (y i) := rfl
theorem allTransfers_apply (x : S) (i : I) : allTransfers t x i = t i x := rfl

variable (hsplit : ∀ i y, t i (p i y) = y)
variable (hcross : ∀ i j, i ≠ j → ∀ y, t i (p j y) = 0)
include hsplit hcross

/-- All component splittings assemble precisely when the cross terms vanish. -/
theorem transfer_sum (y : (i : I) → T i) :
    allTransfers t (sumPullback p y) = y := by
  funext i
  change t i (∑ j, p j (y j)) = y i
  rw [map_sum, Finset.sum_eq_single i]
  · exact hsplit i (y i)
  · intro j _ hji
    exact hcross i j (Ne.symm hji) (y j)
  · simp

/-- Orthogonality alone leaves an explicit common-kernel summand in the source. -/
@[expose] def decomposition : S ≃+ (((i : I) → T i) × (allTransfers t).ker) :=
  SplitAdditiveRetraction318.equivalence (sumPullback p) (allTransfers t)
    (transfer_sum p t hsplit hcross)

theorem decomposition_first (x : S) :
    (decomposition p t hsplit hcross x).1 = allTransfers t x := rfl

theorem decomposition_second (x : S) :
    ((decomposition p t hsplit hcross x).2 : S) =
      x - ∑ i, p i (t i x) := rfl

/-- Cross-term vanishing proves independence, not exhaustion of the source. -/
theorem sumPullback_injective : Function.Injective (sumPullback p) :=
  Function.LeftInverse.injective (transfer_sum p t hsplit hcross)

/-- The remaining spanning obligation is exactly that all transfers detect zero. -/
theorem surjective_iff_commonKernel_zero :
    Function.Surjective (sumPullback p) ↔
      ∀ x : S, (∀ i, t i x = 0) → x = 0 := by
  constructor
  · intro hsurj x hx
    obtain ⟨y, hy⟩ := hsurj x
    have hyzero : y = 0 := by
      have h := transfer_sum p t hsplit hcross y
      rw [hy] at h
      funext i
      exact (congrFun h i).symm.trans (hx i)
    rw [← hy, hyzero, map_zero]
  · intro hker x
    refine ⟨allTransfers t x, ?_⟩
    have hzero : x - sumPullback p (allTransfers t x) = 0 := by
      apply hker
      intro i
      rw [map_sub]
      have h := congrFun (transfer_sum p t hsplit hcross (allTransfers t x)) i
      change t i (sumPullback p (allTransfers t x)) = t i x at h
      rw [h, sub_self]
    exact (sub_eq_zero.mp hzero).symm

/-- This equivalence is conditional on both genuinely separate geometric inputs. -/
@[expose] def equivalence
    (hker : ∀ x : S, (∀ i, t i x = 0) → x = 0) : ((i : I) → T i) ≃+ S :=
  AddEquiv.ofBijective (sumPullback p)
    ⟨sumPullback_injective p t hsplit hcross,
      (surjective_iff_commonKernel_zero p t hsplit hcross).mpr hker⟩

theorem equivalence_apply
    (hker : ∀ x : S, (∀ i, t i x = 0) → x = 0) (y : (i : I) → T i) :
    equivalence p t hsplit hcross hker y = ∑ i, p i (y i) := rfl

theorem equivalence_symm_apply
    (hker : ∀ x : S, (∀ i, t i x = 0) → x = 0) (x : S) :
    (equivalence p t hsplit hcross hker).symm x = allTransfers t x := by
  have h := transfer_sum p t hsplit hcross
    ((equivalence p t hsplit hcross hker).symm x)
  change allTransfers t
    ((equivalence p t hsplit hcross hker)
      ((equivalence p t hsplit hcross hker).symm x)) = _ at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end FiniteSplitTransfer318
