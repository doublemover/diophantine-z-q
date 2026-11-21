module
public import ActualGaussianWeberIntegralPrimeAbove318
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section

namespace ActualGaussianWeberIntegerModel318

open NumberField IsDedekindDomain
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberIntegralPrimeAbove318

theorem gaussianI_integral : IsIntegral ℤ gaussianI := by
  apply IsIntegral.of_pow (by decide : 0<(2:ℕ))
  rw [gaussianI_sq]
  exact isIntegral_one.neg

theorem gaussian_integral (z : GaussianInt) : IsIntegral ℤ z := by
  obtain ⟨a,b⟩ := z
  have h : literal a b=(a:GaussianInt)+gaussianI*(b:GaussianInt) := Zsqrtd.decompose
  change IsIntegral ℤ (literal a b)
  rw [h]
  exact (isIntegral_algebraMap (x:=a)).add (gaussianI_integral.mul (isIntegral_algebraMap (x:=b)))

/-- Literal Gaussian integers are the integral closure of ℤ in the
same Gaussian fraction field used by the chosen prime and complex map. -/
instance gaussianIntegralClosure : IsIntegralClosure GaussianInt ℤ Base where
  algebraMap_injective := IsFractionRing.injective GaussianInt Base
  isIntegral_iff := by
    intro x
    constructor
    · intro h
      exact (IsIntegrallyClosed.isIntegral_iff (R:=GaussianInt)).mp
        (IsIntegral.tower_top (A:=GaussianInt) h)
    · rintro ⟨z,rfl⟩
      exact (gaussian_integral z).algebraMap

variable {L : Type*} [Field L]

/-- Literal base embedding restricted to the fixed extension's
ring of integers. A number-ring model is not supplied separately. -/
@[expose] def integralEmbedding (f : Base→+*L) : GaussianInt→+*𝓞 L where
  toFun z := ⟨f (algebraMap GaussianInt Base z),
    map_isIntegral_int (f.comp (algebraMap GaussianInt Base)) (gaussian_integral z)⟩
  map_zero' := by
    apply RingOfIntegers.ext
    change f (algebraMap GaussianInt Base 0)=0
    rw [map_zero,map_zero]
  map_one' := by
    apply RingOfIntegers.ext
    change f (algebraMap GaussianInt Base 1)=1
    rw [map_one,map_one]
  map_add' x y := by
    apply RingOfIntegers.ext
    change f (algebraMap GaussianInt Base (x+y))=
      f (algebraMap GaussianInt Base x)+f (algebraMap GaussianInt Base y)
    rw [map_add,map_add]
  map_mul' x y := by
    apply RingOfIntegers.ext
    change f (algebraMap GaussianInt Base (x*y))=
      f (algebraMap GaussianInt Base x)*f (algebraMap GaussianInt Base y)
    rw [map_mul,map_mul]

theorem integral_to_field (f : Base→+*L) (z : GaussianInt) :
    algebraMap (𝓞 L) L (integralEmbedding f z)=f (algebraMap GaussianInt Base z) := rfl

theorem integralEmbedding_injective (f : Base→+*L) : Function.Injective (integralEmbedding f) := by
  intro x y h
  apply IsFractionRing.injective GaussianInt Base
  apply f.injective
  simpa only [integral_to_field] using congrArg (algebraMap (𝓞 L) L) h

@[expose] def integralAlgebra (f : Base→+*L) : Algebra GaussianInt (𝓞 L) :=
  (integralEmbedding f).toAlgebra

theorem integralFaithful (f : Base→+*L) :
    letI := integralAlgebra f
    FaithfulSMul GaussianInt (𝓞 L) := by
  letI := integralAlgebra f
  apply (faithfulSMul_iff_algebraMap_injective GaussianInt (𝓞 L)).mpr
  change Function.Injective (integralEmbedding f)
  exact integralEmbedding_injective f

theorem integralExtension (f : Base→+*L) :
    letI := integralAlgebra f
    Algebra.IsIntegral GaussianInt (𝓞 L) := by
  letI := integralAlgebra f
  constructor
  intro x
  exact IsIntegral.tower_top (A:=GaussianInt) (RingOfIntegers.isIntegral x)

variable [NumberField L]
variable {p : ℕ} [Fact p.Prime]

/-- A selected prime above the actual original generator exists in
the literal number ring and its residue quotient is finite. -/
theorem exists_signed_number_place (f : Base→+*L) (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    letI := integralAlgebra f
    ∃ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.under GaussianInt=Ideal.span {literal a b} ∧ Finite (𝓞 L ⧸ w.asIdeal) := by
  letI := integralAlgebra f
  letI := integralFaithful f
  letI := integralExtension f
  obtain ⟨w,hw⟩ := exists_chosen_prime_above (S:=𝓞 L) (rootOf (p:=p) a b)
    (rootOf_sq a b hn)
  exact ⟨w,hw.trans (original_pair_selected_ideal a b hn),
    Ring.HasFiniteQuotients.finiteQuotient w.ne_bot⟩

end ActualGaussianWeberIntegerModel318
