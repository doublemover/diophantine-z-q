module
public import OriginalAllPrimeDlog318
public import OriginalIntegerAffineExtend318
public import OriginalIntegralFrameLocalize318
public section
noncomputable section

namespace OriginalAllPrimeAffineSections318
open SelectedActualSameAFiniteDlogRows318 SelectedSameADyadicVerticalD2_318
open OriginalAllPrimeDlog318 OriginalIntegerAffineExtend318 OriginalIntegralFrameLocalize318
variable {K : Type*} [Field K]

/-- Structural height-one local ring, inside the original function field.
There is intentionally no assumption about a selected physical trait,
a section at the prime, log derivative, or local frame/pullback reading. -/
structure OriginalStalk (A : Subring K) (q : Ideal A) [q.IsPrime] (p : ℕ) where
  V : Subring K
  hAV : A≤V
  localization : letI := (Subring.inclusion hAV).toAlgebra; IsLocalization q.primeCompl V
  dvr : IsDiscreteValuationRing V
  fraction : IsFractionRing V K
  p_nonunit : ¬IsUnit (p:V)
  reduced : IsReduced (V ⧸ Ideal.span ({(p:V)} : Set V))

variable [CharZero K] [Algebra ℚ K]
/-- Reconstructed in the SAME ambient field from a single affine
relative frame. This proves both SHARP sections belong to A, not merely
to an extension, a generic fibre, or a family of unrelated local rings. -/
theorem original_affine_sections (A : Subring K) [IsFractionRing A K]
    (G : Subring K) (hAG : A≤G)
    (generic : letI := (Subring.inclusion hAG).toAlgebra; IsLocalization (positiveIntegers A) G)
    (fibre : ∀ p : ℕ,p.Prime → IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (places : ∀ p : ℕ, p.Prime → ∀ (q : Ideal A)
      (hq : (Ideal.span ({(p:A)} : Set A)).IsMinimalPrime q),
      letI : q.IsPrime := hq.isPrime; Nonempty (OriginalStalk A q p))
    (frame : KaehlerDifferential ℤ A →ₗ[A] A) (t : K)
    (roots : Fin 4 → K) (twists : Fin 4 → ℚˣ)
    (hn : ∀ i,contact t i ≠ 0)
    (he : ∀ i,(roots i)^2=algebraMap ℚ K (twists i:ℚ)*contact t i)
    (hgeneric :
      (25725/4:K)*32*qcoeff t (fractionDerivative A frame t)∈G ∧
      (25725/4:K)*t*qcoeff t (fractionDerivative A frame t)∈G) :
      (25725/4:K)*32*qcoeff t (fractionDerivative A frame t)∈A ∧
      (25725/4:K)*t*qcoeff t (fractionDerivative A frame t)∈A := by
  let D := fractionDerivative A frame
  let x0 : K := (25725/4:K)*32*qcoeff t (D t)
  let x1 : K := (25725/4:K)*t*qcoeff t (D t)
  have hA : ∀ z∈A,D z∈A := by
    intro z h
    let y : A := ⟨z,h⟩
    change fractionDerivative A frame (y:K)∈A
    rw [fractionDerivative_apply]
    exact (frame (KaehlerDifferential.D ℤ A y)).property
  have stalk (p : ℕ) (hp : p.Prime) (q : Ideal A)
      (hq : (Ideal.span ({(p:A)} : Set A)).IsMinimalPrime q) :
      HasStalkValue A q x0 ∧ HasStalkValue A q x1 := by
    let : q.IsPrime := hq.isPrime
    obtain ⟨l⟩ := places p hp q hq
    let V := l.V
    let : IsDiscreteValuationRing V := l.dvr
    let : IsFractionRing V K := l.fraction
    let : IsReduced (V ⧸ Ideal.span ({(p:V)} : Set V)) := l.reduced
    have hv : ∀ z∈V,D z∈V := preserves_stalk A q V l.hAV l.localization D hA
    let vframe := (restrictD V D hv).liftKaehlerDifferential
    have fd : fractionDerivative V vframe=D := field_localize V D hv
    obtain ⟨d,_,h0,h1⟩ := sharp_sections_at_vertical V p hp.ne_zero l.p_nonunit vframe t
      roots twists hn he
    rw [fd] at h0 h1
    change ((row0 d:V):K)=x0 at h0
    change ((row1 d:V):K)=x1 at h1
    exact ⟨from_localization A V l.hAV l.localization (h0 ▸ (row0 d).property),
      from_localization A V l.hAV l.localization (h1 ▸ (row1 d).property)⟩
  obtain ⟨N₀,hn₀,a₀,ha₀⟩ := denominator_of_generic A G hAG generic hgeneric.1
  obtain ⟨N₁,hn₁,a₁,ha₁⟩ := denominator_of_generic A G hAG generic hgeneric.2
  exact ⟨extend_from_single_integer A x0 N₀ hn₀ a₀ ha₀ (fun p hp _ => fibre p hp)
      (fun p hp _ q hq => (stalk p hp q hq).1),
    extend_from_single_integer A x1 N₁ hn₁ a₁ ha₁ (fun p hp _ => fibre p hp)
      (fun p hp _ q hq => (stalk p hp q hq).2)⟩

end OriginalAllPrimeAffineSections318
