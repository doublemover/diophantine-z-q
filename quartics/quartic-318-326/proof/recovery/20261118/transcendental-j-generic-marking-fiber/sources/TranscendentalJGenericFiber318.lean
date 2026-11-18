module
public import ActualLargeJRealization318
public import OpenJAnalyticPoints318
public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace TranscendentalJGenericFiber318
open OpenJComplexEvaluation318 Function

/-- Transcendentals occur at arbitrarily large absolute value, even on a
horizontal line. This is about the arithmetic function field, not the
generic point over the strictly larger ground field of complex constants. -/
theorem large_transcendental (M : ℝ) :
    ∃ c : ℂ, M < ‖c‖ ∧ Transcendental ℤ c := by
  let f (x:ℝ) : ℂ := ⟨x,max M 0+1⟩
  have hi : Injective f := fun _ _ h => congrArg Complex.re h
  have hc := (Algebraic.countable ℤ ℂ).preimage hi
  obtain ⟨x,hx⟩ : ∃ x:ℝ, ¬ IsAlgebraic ℤ (f x) := by
    by_contra! hall
    apply Set.not_countable_univ (α:=ℝ)
    exact hc.mono (fun a _ => hall a)
  refine ⟨f x,?_,hx⟩
  have hb := Complex.abs_im_le_norm (f x)
  change |max M 0 + 1| ≤ ‖f x‖ at hb
  rw [abs_of_nonneg (by linarith [le_max_right M (0:ℝ)] : 0≤max M 0+1)] at hb
  linarith [le_max_left M (0:ℝ)]

/-- These are honest analytic periods, not an assumption that the complex
j-map is the affine coordinate on the full compact modular curve. -/
theorem exists_period (M:ℝ) : ∃ τ:UpperHalfPlane,
    M<‖ActualQJ318.jInvariant τ‖ ∧ Admissible τ ∧
    Transcendental ℤ (ActualQJ318.jInvariant τ) := by
  obtain ⟨M₀,hM⟩ := ActualLargeJRealization318.all_large
  obtain ⟨c,hc,ht⟩ := large_transcendental (max M₀ (max M 1728))
  obtain ⟨τ,hτ⟩ := hM c ((le_max_left _ _).trans_lt hc)
  have h1 := (le_max_right M₀ (max M 1728)).trans_lt hc
  have h2 := (le_max_right M 1728).trans_lt h1
  refine ⟨τ,by rw [hτ];exact (le_max_left _ _).trans_lt h1,?_,by rwa [hτ]⟩
  change ActualQJ318.jInvariant τ ≠ 0 ∧ ActualQJ318.jInvariant τ ≠ 1728
  rw [hτ]
  constructor <;> intro hh <;> rw [hh] at h2 <;> norm_num at h2

variable (N:ℕ) [NeZero N]
instance baseDomain : IsDomain (OpenJModel318.Base N) := by
  apply Localization.Away.isDomain
  obtain ⟨τ,_,h,_⟩ := exists_period 0
  intro hz
  have hh := denominator_isUnit N τ h
  rw [hz,map_zero] at hh
  exact not_isUnit_zero hh

abbrev K := FractionRing (OpenJModel318.Base N)
variable (τ:UpperHalfPlane) (h:Admissible τ)
variable (ht:Transcendental ℤ (ActualQJ318.jInvariant τ))

theorem evaluation_injective : Injective (evaluation N τ h) := by
  have hp : Injective (polynomialEval τ) := transcendental_iff_injective.mp ht
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (OpenJModel318.denominator N)) (evaluation N τ h)).mpr
  intro x y
  refine ⟨fun hh=>congrArg (evaluation N τ h) hh,?_⟩
  intro hh
  simp only [evaluation,IsLocalization.Away.lift_eq] at hh
  exact congrArg _ (hp hh)

/-- The true generic arithmetic field embeds in ℂ at this period. -/
def embedding : K N →+* ℂ := IsFractionRing.lift (evaluation_injective N τ h ht)

@[simp] theorem embedding_base (b:OpenJModel318.Base N) :
    embedding N τ h ht (algebraMap _ (K N) b)=evaluation N τ h b :=
  IsFractionRing.lift_algebraMap _ _

/-- The same arithmetic elliptic curve: base change of the generic curve
agrees coefficientwise with the original honest complex evaluation. -/
theorem actual_curve :
    ((OpenJModel318.integralModel N).map (algebraMap _ (K N))).map (embedding N τ h ht)
      = fiber N τ h := by
  ext <;> simp [fiber,WeierstrassCurve.map]
end TranscendentalJGenericFiber318
