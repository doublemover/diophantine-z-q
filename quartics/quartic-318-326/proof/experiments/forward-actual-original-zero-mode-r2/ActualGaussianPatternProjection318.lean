module
public import ActualGaussianAllSignsTail318
public section
noncomputable section
namespace ActualGaussianPatternProjection318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralSliceBoxCount318 ActualGaussianSignAction318
open ActualGaussianAllSignsTail318 ActualGaussianGrowingCutoff318 OriginalWeightedSelberg318
set_option maxHeartbeats 14000000

/-- Actual (u,w) patterns admitting original Gaussian generators at the
specified two distinct coefficient positions. The witness retains all
five coordinates, both norms, the original box and actual signed obstruction. -/
@[expose] def Pattern (B : ℕ) (ci cj : ℤ) (Y : ℕ) :=
  {z : ℤ×ℤ // ∃ v : SignedSource B (ci-cj) Y,
    v.1.1.2.2=z.2 ∧ v.1.1.1.1^2+v.1.1.1.2^2=z.1+ci*z.2^2}

/-- Literal generator witnesses enter the counted pattern directly.
No choice of Gaussian generator is imposed by this upper bound. -/
theorem of_actual_generators (B : ℕ) (ci cj u w a b c d : ℤ) (Y : ℕ)
    (hfirst : a^2+b^2=u+ci*w^2) (hsecond : c^2+d^2=u+cj*w^2)
    (hbox : InBox B ((a,b),(c,d),w))
    (hbad : ∃ s t : Bool, ∃ p : ℕ, p.Prime ∧ Y<p ∧
      (p:ℤ)∣(a+sign s)^2+b^2 ∧ (p:ℤ)∣(c+sign t)^2+d^2) :
    ∃ z : Pattern B ci cj Y, z.1=(u,w) := by
  let v : Quadric (ci-cj) := ⟨((a,b),(c,d),w),by
    dsimp [equation]
    linear_combination hfirst-hsecond⟩
  exact ⟨⟨(u,w),⟨v,hbox,hbad⟩,rfl,hfirst⟩,rfl⟩

@[expose] def choice (B : ℕ) (ci cj : ℤ) (Y : ℕ) :
    Pattern B ci cj Y → SignedSource B (ci-cj) Y := fun z => z.2.choose
lemma choice_w (B : ℕ) (ci cj : ℤ) (Y : ℕ) (z : Pattern B ci cj Y) :
    (choice B ci cj Y z).1.1.2.2=z.1.2 := z.2.choose_spec.1
lemma choice_norm (B : ℕ) (ci cj : ℤ) (Y : ℕ) (z : Pattern B ci cj Y) :
    (choice B ci cj Y z).1.1.1.1^2+(choice B ci cj Y z).1.1.1.2^2=
      z.1.1+ci*z.1.2^2 := z.2.choose_spec.2
lemma choice_injective (B : ℕ) (ci cj : ℤ) (Y : ℕ) :
    Function.Injective (choice B ci cj Y) := by
  intro z z' he
  have hw : z.1.2=z'.1.2 := by
    have hh := congrArg (fun v : SignedSource B (ci-cj) Y => v.1.1.2.2) he
    simpa only [choice_w] using hh
  have hn := choice_norm B ci cj Y z
  have hn' := choice_norm B ci cj Y z'
  rw [he] at hn
  apply Subtype.ext
  apply Prod.ext
  · rw [hw] at hn
    linarith
  · exact hw
instance pattern_finite (B : ℕ) (ci cj : ℤ) (Y : ℕ) : Finite (Pattern B ci cj Y) :=
  Finite.of_injective (choice B ci cj Y) (choice_injective B ci cj Y)

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def coefficients (c : J → ℤ) (ci : ℤ) : J → ℤ := fun j => c j-ci
@[expose] def patternWeight (c : J → ℤ) (z : ℤ×ℤ) : ℝ :=
  ∏ j, Real.log (max 1 (((z.1+c j*z.2^2).natAbs:ℝ)))
lemma patternWeight_nonneg (c : J → ℤ) (z : ℤ×ℤ) : 0≤patternWeight c z := by
  apply Finset.prod_nonneg
  intro j _
  exact Real.log_nonneg (le_max_left _ _)

/-- All ORIGINAL form values, not only a comparison weight, are recovered
from this same (u,w) and the chosen first Gaussian generator. -/
lemma actual_form_values (B : ℕ) (ci cj : ℤ) (Y : ℕ) (c : J → ℤ)
    (z : Pattern B ci cj Y) (j : J) :
    form (ci-cj) (coefficients c ci) j (choice B ci cj Y z).1=z.1.1+c j*z.1.2^2 := by
  have hn := choice_norm B ci cj Y z
  dsimp only [form,coefficients]
  rw [choice_w]
  linear_combination hn
lemma actual_weight_identity (B : ℕ) (ci cj : ℤ) (Y : ℕ) (c : J → ℤ)
    (z : Pattern B ci cj Y) :
    weight (ci-cj) (coefficients c ci) (choice B ci cj Y z).1=patternWeight c z.1 := by
  apply Finset.prod_congr rfl
  intro j _
  rw [actual_form_values]

@[expose] def patternMass (B : ℕ) (ci cj : ℤ) (Y : ℕ) (c : J → ℤ) : ℝ := by
  classical
  letI : Fintype (Pattern B ci cj Y) := Fintype.ofFinite _
  exact ∑ z : Pattern B ci cj Y,patternWeight c z.1

/-- Genuine original pattern projection, with arbitrary generator
choices already covered. Distinct patterns inject into the original
source since w and a²+b²-ci*w² recover (u,w). -/
theorem actual_pattern_tail (B : ℕ) (hB : 1≤B) (ci cj : ℤ) (hc : ci≠cj)
    (Y : ℕ) (hY : cutoff (ci-cj) B≤Y) (c : J → ℤ) :
    patternMass B ci cj Y c≤4*growingConstant (ci-cj) (coefficients c ci)*
      (B:ℝ)^(3-(1:ℝ)/200) := by
  classical
  letI : Fintype (Pattern B ci cj Y) := Fintype.ofFinite _
  letI : Fintype (SignedSource B (ci-cj) Y) := Fintype.ofFinite _
  have hh := hasSum_le_inj (choice B ci cj Y) (choice_injective B ci cj Y)
    (fun v _ => weight_nonneg (ci-cj) (coefficients c ci) v.1)
    (fun z => le_of_eq (actual_weight_identity B ci cj Y c z).symm)
    (hasSum_fintype (fun z : Pattern B ci cj Y => patternWeight c z.1))
    (hasSum_fintype (fun v : SignedSource B (ci-cj) Y => weight (ci-cj) (coefficients c ci) v.1))
  exact hh.trans (actual_all_signs_tail B hB (ci-cj) (sub_ne_zero.mpr hc) Y hY _)

end ActualGaussianPatternProjection318
