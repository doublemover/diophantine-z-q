module
public import ComplementRootAction318
public section
noncomputable section
open scoped BigOperators
namespace ComplementaryFunctionRigidity318
open ComplementSquareclass318 ComplementRootReconstruction318
open KummerTensorField318 FourRootAutomorphisms318
variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- On an actual root family, the same complement formula is its exact inverse. -/
theorem recover_original (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) (x : Fin 4 → L)
    (hx : ∀ i, x i ^ 2 = algebraMap F L (a i)) (i : Fin 4) :
    recovered a (complementaryProduct x) i = x i := by
  have hp : allProduct x ^ 2 = algebraMap F L (allProduct a) := by
    simp only [allProduct, ← Finset.prod_pow, hx, map_prod]
  rw [recovered, complement_twice, hp]
  exact mul_div_cancel_right₀ _ (denominator_ne_zero a ha)

lemma map_recovered {M : Type*} [Field M] [Algebra F M]
    (a : Fin 4 → F) (z : Fin 4 → L) (f : L →ₐ[F] M) (i : Fin 4) :
    f (recovered a z i) = recovered a (fun j => f (z j)) i := by
  simp only [recovered, complementaryProduct, map_div, map_prod, f.commutes]

/-- The four original complementary functions determine the map on the whole
field; equality of their squares would not be sufficient here. -/
theorem hom_ext_complementary (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    [Fact (QuadraticTower318.Independent a)] {f g : Raw a →ₐ[F] L}
    (h : ∀ i, f (FourRootEvaluation318.characterGenerator a i) =
      g (FourRootEvaluation318.characterGenerator a i)) : f = g := by
  letI : Field (Raw a) := (actual_field a).toField
  apply FourRootEvaluation318.hom_ext
  intro i
  rw [← recover_original a ha (generator a) (generator_square a) i,
    map_recovered, map_recovered]
  congr 1
  funext j
  exact h j

lemma sign_complementary (a : Fin 4 → F) (s : Fin 4 → Bool) (i : Fin 4) :
    signEquiv a s (FourRootEvaluation318.characterGenerator a i) =
      algebraMap F (Raw a) (complementaryProduct (ComplementRootAction318.sign s) i) *
        FourRootEvaluation318.characterGenerator a i := by
  simp only [FourRootEvaluation318.characterGenerator, complementaryProduct, map_prod, signEquiv_generator, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases hs : s (SourceTwistArithmetic318.complement i j)
  · simp [ComplementRootAction318.sign, hs]
  · simp only [hs, Bool.true_eq_false, ite_true, ComplementRootAction318.sign,
      map_neg, map_one]
    change -generator a (SourceTwistArithmetic318.complement i j) =
      -(1 : Raw a) * generator a (SourceTwistArithmetic318.complement i j)
    exact (neg_one_mul _).symm

/-- Equality on the old quadratic functions, with the explicit base-field
scales retained, forces the full original root-sign action under the SAME
field equivalence. No new equivariant replacement map is chosen. -/
theorem equivariant (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    [Fact (QuadraticTower318.Independent a)] (e : Raw a ≃ₐ[F] L)
    (u : Fin 4 → F) (hu : ∀ i, u i ≠ 0) (y : Fin 4 → L)
    (hy : ∀ i, e (FourRootEvaluation318.characterGenerator a i) * algebraMap F L (u i) = y i)
    (σ : L ≃ₐ[F] L) (s : Fin 4 → Bool)
    (hσ : ∀ i, σ (y i) =
      algebraMap F L (complementaryProduct (ComplementRootAction318.sign s) i) * y i)
    (z : Raw a) : σ (e z) = e (signEquiv a s z) := by
  have h : σ.toAlgHom.comp e.toAlgHom = e.toAlgHom.comp (signEquiv a s).toAlgHom := by
    apply hom_ext_complementary a ha
    intro i
    change σ (e (FourRootEvaluation318.characterGenerator a i)) =
      e (signEquiv a s (FourRootEvaluation318.characterGenerator a i))
    rw [sign_complementary, map_mul, e.commutes]
    have hm : algebraMap F L (u i) ≠ 0 := by
      simpa only [map_zero] using (algebraMap F L).injective.ne (hu i)
    apply mul_right_cancel₀ hm
    have hh := hσ i
    rw [← hy i, map_mul, σ.commutes] at hh
    simpa only [mul_assoc] using hh
  exact congrArg (fun f : Raw a →ₐ[F] L => f z) h
end ComplementaryFunctionRigidity318
