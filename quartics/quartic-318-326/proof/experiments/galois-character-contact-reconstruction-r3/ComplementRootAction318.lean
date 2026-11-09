module
public import ComplementRootReconstruction318
public section
noncomputable section
open scoped BigOperators
namespace ComplementRootAction318
open ComplementSquareclass318 ComplementRootReconstruction318
variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

lemma allProduct_square (s : Fin 4 → F) (hs : ∀ i, s i ^ 2 = 1) :
    allProduct s ^ 2 = 1 := by
  simp only [allProduct, ← Finset.prod_pow, hs, Finset.prod_const_one]

/-- The four complementary characters are inverted on the SAME supplied field
and action. The full-product square factor is computed, not suppressed. -/
theorem recovered_action (a : Fin 4 → F) (z : Fin 4 → L) (s : Fin 4 → F)
    (hs : ∀ i, s i ^ 2 = 1) (e : L ≃ₐ[F] L)
    (he : ∀ i, e (z i) = algebraMap F L (complementaryProduct s i) * z i)
    (i : Fin 4) :
    e (recovered a z i) = algebraMap F L (s i) * recovered a z i := by
  have hp : e (complementaryProduct z i) =
      algebraMap F L (complementaryProduct (complementaryProduct s) i) *
        complementaryProduct z i := by
    simp only [complementaryProduct, map_prod, he, Finset.prod_mul_distrib]
  simp only [recovered, map_div, e.commutes]
  rw [hp, complement_twice, allProduct_square s hs, mul_one]
  all_goals ring

@[expose] def sign (s : Fin 4 → Bool) (i : Fin 4) : F := if s i then -1 else 1

lemma sign_square (s : Fin 4 → Bool) (i : Fin 4) : sign (F := F) s i ^ 2 = 1 := by
  unfold sign
  split <;> simp

/-- This identifies the original root-sign map with a given geometric action
only when the latter's complementary-root formulas have actually been supplied. -/
theorem evaluation_equivariant (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (z : Fin 4 → L)
    (hz : ∀ i, z i ^ 2 = algebraMap F L (complementaryProduct a i))
    (s : Fin 4 → Bool) (e : L ≃ₐ[F] L)
    (he : ∀ i, e (z i) = algebraMap F L (complementaryProduct (sign s) i) * z i)
    (w : KummerTensorField318.Raw a) :
    e (evaluate a ha z hz w) = evaluate a ha z hz (FourRootAutomorphisms318.signEquiv a s w) := by
  apply FourRootEvaluation318.equivariant
  intro i
  have h := recovered_action a z (sign s) (sign_square s) e he i
  simpa [sign] using h
end ComplementRootAction318
