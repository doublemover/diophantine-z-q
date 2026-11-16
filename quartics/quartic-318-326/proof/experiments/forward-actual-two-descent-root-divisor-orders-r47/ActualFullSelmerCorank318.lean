module
public import ActualPontryaginLowCorank318
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.GroupTheory.OrderOfElement
public section
noncomputable section
namespace ActualFullSelmerCorank318
open ActualTwoDescentDiscreteSelmerDual318 ActualTwoDescentPontryaginPadicModule318
open ActualPontryaginLowCorank318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- A finite additive module over a characteristic-zero ring has rank zero.
The annihilating scalar comes from each element's actual finite additive
order and is nonzero in the scalar ring. -/
theorem rank_zero_of_finite_charZero (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] : Module.rank R M = 0 := by
  apply rank_eq_zero_iff.mpr
  intro x
  obtain ⟨q, hq, hqx⟩ := (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  refine ⟨(q : R), Nat.cast_ne_zero.mpr hq.ne', ?_⟩
  simpa only [Nat.cast_smul_eq_nsmul] using hqx

/-- Full 2-primary Selmer corank means the rank of the ACTUAL native
Pontryagin dual under its already defined natural Z2 action. This definition
is not the rational-point rank or the size of a single finite Selmer level. -/
def actualFullSelmerCorank (n : ℚ) (hn : n ≠ 0) : Cardinal :=
  letI := actualPontryaginPadicModule n hn
  Module.rank ℤ_[2] (Additive (ActualPontryagin n hn))

/-- Concrete corank control for the full actual Selmer dual, without an
assumed reduced pairing or pointwise converse. The two values remain an
unresolved alternative for any particular twist. -/
theorem actual_full_selmer_corank_zero_or_one (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    actualFullSelmerCorank n hn = 0 ∨ actualFullSelmerCorank n hn = 1 := by
  letI := actualPontryaginPadicModule n hn
  rcases actual_pontryagin_finite_or_linear_z2 n hn hf hb hS with h | ⟨e⟩
  · letI := h
    exact Or.inl (rank_zero_of_finite_charZero ℤ_[2] (Additive (ActualPontryagin n hn)))
  · right
    change Module.rank ℤ_[2] (Additive (ActualPontryagin n hn)) = 1
    rw [e.rank_eq, CommSemiring.rank_self]

theorem actual_full_selmer_corank_le_one (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn) = 8) :
    actualFullSelmerCorank n hn ≤ 1 := by
  rcases actual_full_selmer_corank_zero_or_one n hn hf hb hS with h | h
  · rw [h]; exact zero_le _
  · rw [h]

end ActualFullSelmerCorank318
