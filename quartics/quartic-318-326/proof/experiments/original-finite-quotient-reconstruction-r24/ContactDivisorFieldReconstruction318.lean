module
public import RationalFunctionEvenSquare318
public import SquareclassRadicalNormalization318
public section
noncomputable section
open scoped BigOperators
namespace ContactDivisorFieldReconstruction318
open ComplementSquareclass318

/-- The exact complementary branch polynomials in the original coordinate t. -/
@[expose] def contactProduct (i : Fin 4) : RatFunc ℚ :=
  complementaryProduct (SourceKummerField318.parameter (fun _ => 1)) i

lemma contactProduct_ne_zero (i : Fin 4) : contactProduct i ≠ 0 := by
  change (∏ j : Fin 3, SourceKummerField318.parameter (fun _ => 1)
    (SourceTwistArithmetic318.complement i j)) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
    LabeledContactFieldReconstruction318.parameter_ne_zero (fun _ => 1)
      (SourceTwistArithmetic318.complement i j))

lemma parameter_twist (c : Fin 4 → ℚˣ) (i : Fin 4) :
    SourceKummerField318.parameter c i =
      RatFunc.C (c i : ℚ) * SourceKummerField318.parameter (fun _ => 1) i := by
  simp only [SourceKummerField318.parameter, map_mul, RatFunc.algebraMap_C,
    Units.val_one, map_one, one_mul]

lemma complementary_twist (c : Fin 4 → ℚˣ) (i : Fin 4) :
    complementaryProduct (SourceKummerField318.parameter c) i =
      RatFunc.C (complementaryProduct (fun j => (c j : ℚ)) i) * contactProduct i := by
  change (∏ j : Fin 3, SourceKummerField318.parameter c
      (SourceTwistArithmetic318.complement i j)) =
    RatFunc.C (∏ j : Fin 3, (c (SourceTwistArithmetic318.complement i j) : ℚ)) *
      ∏ j : Fin 3, SourceKummerField318.parameter (fun _ => 1)
        (SourceTwistArithmetic318.complement i j)
  calc
    _ = ∏ j : Fin 3, RatFunc.C (c (SourceTwistArithmetic318.complement i j) : ℚ) *
        SourceKummerField318.parameter (fun _ => 1)
          (SourceTwistArithmetic318.complement i j) := by
      apply Finset.prod_congr rfl
      intro j _
      exact parameter_twist c (SourceTwistArithmetic318.complement i j)
    _ = (∏ j : Fin 3, RatFunc.C (c (SourceTwistArithmetic318.complement i j) : ℚ)) *
        (∏ j : Fin 3, SourceKummerField318.parameter (fun _ => 1)
          (SourceTwistArithmetic318.complement i j)) := by rw [Finset.prod_mul_distrib]
    _ = _ := by rw [map_prod]

/-- The all-prime even-divisor hypothesis recovers consistent FOUR contact
radicands from the FOUR complementary quadratic functions. The twist constants
are reconstructed, not silently set equal to the fixed arithmetic model. -/
theorem squareclasses_from_branch_parity (b : Fin 4 → RatFunc ℚ) (hb : ∀ i, b i ≠ 0)
    (hparity : ∀ i (q : Polynomial ℚ), Prime q →
      Even (RationalFunctionEvenSquare318.orderAt q (b i / contactProduct i))) :
    ∃ c : Fin 4 → ℚˣ, ∀ i,
      IsSquare (b i / complementaryProduct (SourceKummerField318.parameter c) i) := by
  have hex := fun i => RationalFunctionEvenSquare318.scalar_square
    (b i / contactProduct i) (div_ne_zero (hb i) (contactProduct_ne_zero i)) (hparity i)
  choose d g hd hg hf using hex
  have hc : ∀ i, complementaryProduct d i ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hd _)
  let c : Fin 4 → ℚˣ := fun i => Units.mk0 (complementaryProduct d i) (hc i)
  have hD : allProduct d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  have hDC : RatFunc.C (allProduct d) ≠ 0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne hD
  refine ⟨c, ?_⟩
  intro i
  have he : b i = (RatFunc.C (d i) * g i ^ 2) * contactProduct i :=
    (div_eq_iff (contactProduct_ne_zero i)).mp (hf i)
  have ht : complementaryProduct (fun j => (c j : ℚ)) i = d i * allProduct d ^ 2 := by
    change complementaryProduct (complementaryProduct d) i = _
    exact complement_twice d i
  have hdC : RatFunc.C (d i) ≠ 0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne (hd i)
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨g i / RatFunc.C (allProduct d), ?_⟩
  rw [he, complementary_twist, ht, map_mul, map_pow]
  field_simp [contactProduct_ne_zero i, hdC, hDC] <;> ring

variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L] [FiniteDimensional (RatFunc ℚ) L]

/-- The full algebraic reconstruction endpoint. Geometry must supply the
ORIGINAL degree16 field, its four actual quadratic character functions and
ALL finite-place parity equations. The conclusion is an explicit contact-field
isomorphism preserving those original functions up to stated base-field scales.
Neither a PEL curve nor its branch divisor is assumed to have been constructed. -/
theorem reconstruct (b : Fin 4 → RatFunc ℚ) (hb : ∀ i, b i ≠ 0) (y : Fin 4 → L)
    (hy : ∀ i, y i ^ 2 = algebraMap (RatFunc ℚ) L (b i))
    (hdegree : Module.finrank (RatFunc ℚ) L = 16)
    (hparity : ∀ i (q : Polynomial ℚ), Prime q →
      Even (RationalFunctionEvenSquare318.orderAt q (b i / contactProduct i))) :
    ∃ c : Fin 4 → ℚˣ, ∃ u : Fin 4 → RatFunc ℚ, (∀ i, u i ≠ 0) ∧
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ i, e (FourRootEvaluation318.characterGenerator (SourceKummerField318.parameter c) i) *
          algebraMap (RatFunc ℚ) L (u i) = y i := by
  obtain ⟨c, hc⟩ := squareclasses_from_branch_parity b hb hparity
  exact ⟨c, SquareclassRadicalNormalization318.contact_reconstruction c b hb y hy hc hdegree⟩
end ContactDivisorFieldReconstruction318
