module
public import FourRootEvaluation318
public import ComplementSquareclass318
public section
noncomputable section
open scoped BigOperators
namespace ComplementRootReconstruction318
open ComplementSquareclass318 KummerTensorField318
variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]
variable (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) (z : Fin 4 → L)
  (hz : ∀ i, z i ^ 2 = algebraMap F L (complementaryProduct a i))

/-- The denominator is the old full product of radicands, not a chosen square root. -/
@[expose] def recovered (i : Fin 4) : L :=
  complementaryProduct z i / algebraMap F L (allProduct a)

include ha in
lemma denominator_ne_zero : algebraMap F L (allProduct a) ≠ 0 := by
  have h : allProduct a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)
  simpa only [map_zero] using (algebraMap F L).injective.ne h

include ha hz in
/-- Complementing twice recovers each original root, with the exact denominator retained. -/
theorem recovered_square (i : Fin 4) : recovered a z i ^ 2 = algebraMap F L (a i) := by
  have h : complementaryProduct z i ^ 2 =
      algebraMap F L (complementaryProduct (complementaryProduct a) i) := by
    simp only [complementaryProduct, ← Finset.prod_pow, hz, map_prod]
  rw [recovered, div_pow, h, complement_twice, map_mul, map_pow]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (denominator_ne_zero a ha))

lemma allProduct_complement (b : Fin 4 → F) :
    allProduct (complementaryProduct b) = allProduct b ^ 3 := by
  simp [allProduct, complementaryProduct, SourceTwistArithmetic318.complement,
    Fin.prod_univ_succ] <;> ring

include ha hz in
/-- The reconstructed roots recover the supplied complementary radicals
EXACTLY, including their signs, rather than only their squares. -/
theorem complementary_recovered (i : Fin 4) :
    complementaryProduct (recovered a z) i = z i := by
  have ht : allProduct z ^ 2 = algebraMap F L (allProduct a) ^ 3 := by
    calc
      allProduct z ^ 2 = ∏ j : Fin 4, z j ^ 2 := by
        simp only [allProduct, Finset.prod_pow]
      _ = ∏ j : Fin 4, algebraMap F L (complementaryProduct a j) := by
        simp only [hz]
      _ = algebraMap F L (allProduct (complementaryProduct a)) := by
        rw [allProduct, map_prod]
      _ = algebraMap F L (allProduct a) ^ 3 := by
        rw [allProduct_complement, map_pow]
  calc
    complementaryProduct (recovered a z) i =
        complementaryProduct (complementaryProduct z) i /
          algebraMap F L (allProduct a) ^ 3 := by
      simp only [complementaryProduct, recovered, Finset.prod_div_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = z i := by
      rw [complement_twice, ht]
      exact mul_div_cancel_right₀ _ (pow_ne_zero 3 (denominator_ne_zero a ha))

@[expose] def evaluate : Raw a →ₐ[F] L :=
  FourRootEvaluation318.evaluate a (recovered a z) (recovered_square a ha z hz)

@[simp] theorem evaluate_generator (i : Fin 4) :
    evaluate a ha z hz (FourRootAutomorphisms318.generator a i) =
      complementaryProduct z i / algebraMap F L (allProduct a) :=
  FourRootEvaluation318.evaluate_generator _ _ _ i

/-- The actual evaluation preserves each original complementary quotient
function, not merely an abstract isomorphic quadratic subfield. -/
theorem evaluate_complementary (i : Fin 4) :
    evaluate a ha z hz
      (complementaryProduct (FourRootAutomorphisms318.generator a) i) = z i := by
  simpa only [complementaryProduct, recovered, map_prod, evaluate_generator] using
    complementary_recovered a ha z hz i

variable [hind : Fact (QuadraticTower318.Independent a)] [hfinite : FiniteDimensional F L]

include hind hfinite in
/-- Independence makes the literal evaluation injective; the actual degree16
candidate then forces surjectivity of that SAME homomorphism. -/
theorem evaluate_bijective (hdegree : Module.finrank F L = 16) :
    Function.Bijective (evaluate a ha z hz) := by
  letI : Field (Raw a) := (actual_field a).toField
  have hinj : Function.Injective (evaluate a ha z hz) := (evaluate a ha z hz).injective
  have hd : Module.finrank F (Raw a) = Module.finrank F L :=
    (actual_degree a).trans hdegree.symm
  let e := LinearEquiv.ofInjectiveOfFinrankEq (evaluate a ha z hz).toLinearMap hinj hd
  exact ⟨hinj, e.surjective⟩

/-- An isomorphism onto the original candidate field, with its specified base algebra. -/
@[expose] def equivalence (hdegree : Module.finrank F L = 16) : Raw a ≃ₐ[F] L :=
  AlgEquiv.ofBijective (evaluate a ha z hz) (evaluate_bijective a ha z hz hdegree)

@[simp] theorem equivalence_generator (hdegree : Module.finrank F L = 16) (i : Fin 4) :
    equivalence a ha z hz hdegree (FourRootAutomorphisms318.generator a i) =
      complementaryProduct z i / algebraMap F L (allProduct a) :=
  evaluate_generator a ha z hz i
end ComplementRootReconstruction318
