module
public import LabeledContactFieldReconstruction318
public section
noncomputable section
open scoped BigOperators
namespace SquareclassRadicalNormalization318
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A rational-function squareclass equality normalizes an ACTUAL radical
inside the supplied field. The original radical is retained through z*u=y. -/
theorem normalize (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : IsSquare (b / a)) (y : L) (hy : y ^ 2 = algebraMap F L b) :
    ∃ u : F, u ≠ 0 ∧ ∃ z : L,
      z ^ 2 = algebraMap F L a ∧ z * algebraMap F L u = y := by
  obtain ⟨u, hu⟩ := (isSquare_iff_exists_sq _).mp h
  have he : b = a * u ^ 2 := by
    rw [← hu]
    field_simp [ha] <;> ring
  have hn : u ≠ 0 := by
    intro hzero
    apply hb
    simpa [hzero] using he
  have hm : algebraMap F L u ≠ 0 := by
    simpa only [map_zero] using (algebraMap F L).injective.ne hn
  refine ⟨u, hn, y / algebraMap F L u, ?_, div_mul_cancel₀ y hm⟩
  rw [div_pow, hy, he, map_mul, map_pow]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hm)

variable [CharZero F]
open ComplementSquareclass318

/-- Normalization keeps the original geometric action, since the chosen
scaling lies in the original fixed base field. -/
theorem normalized_action (u : F) (y k : L) (e : L ≃ₐ[F] L)
    (hk : e y = k * y) : e (y / algebraMap F L u) = k * (y / algebraMap F L u) := by
  rw [map_div₀, e.commutes, hk]
  all_goals ring

section Contact
variable {K : Type*} [Field K] [Algebra (RatFunc ℚ) K] [FiniteDimensional (RatFunc ℚ) K]

/-- This consumes squareclasses of the actual four quadratic character
functions, not a claim that an arbitrary field of degree16 is the contact field. -/
theorem contact_reconstruction (c : Fin 4 → ℚˣ) (b : Fin 4 → RatFunc ℚ)
    (hb : ∀ i, b i ≠ 0) (y : Fin 4 → K)
    (hy : ∀ i, y i ^ 2 = algebraMap (RatFunc ℚ) K (b i))
    (hclasses : ∀ i, IsSquare (b i /
      complementaryProduct (SourceKummerField318.parameter c) i))
    (hdegree : Module.finrank (RatFunc ℚ) K = 16) :
    ∃ u : Fin 4 → RatFunc ℚ, (∀ i, u i ≠ 0) ∧
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] K,
        ∀ i, e (FourRootEvaluation318.characterGenerator (SourceKummerField318.parameter c) i) *
          algebraMap (RatFunc ℚ) K (u i) = y i := by
  have ha : ∀ i, complementaryProduct (SourceKummerField318.parameter c) i ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      LabeledContactFieldReconstruction318.parameter_ne_zero c _)
  have h := fun i => normalize _ _ (ha i) (hb i) (hclasses i) (y i) (hy i)
  choose u hu z hz hzy using h
  let d : LabeledContactFieldReconstruction318.RadicalData (L := K) c :=
    ⟨z, hz, hdegree⟩
  refine ⟨u, hu, LabeledContactFieldReconstruction318.equivalence c d, ?_⟩
  intro i
  change ComplementRootReconstruction318.evaluate (SourceKummerField318.parameter c)
    (LabeledContactFieldReconstruction318.parameter_ne_zero c) z hz
    (FourRootEvaluation318.characterGenerator (SourceKummerField318.parameter c) i) *
      algebraMap (RatFunc ℚ) K (u i) = y i
  rw [ComplementRootReconstruction318.evaluate_complementary]
  exact hzy i
end Contact
end SquareclassRadicalNormalization318
