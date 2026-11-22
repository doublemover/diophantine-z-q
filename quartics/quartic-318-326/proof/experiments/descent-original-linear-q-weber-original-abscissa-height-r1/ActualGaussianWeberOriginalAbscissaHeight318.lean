module
public import ActualGaussianWeberEvenAbscissa318
public import ActualGaussianWeberComplexFibreDegree318
public import ActualGaussianWeberOneComplexFibre318
public import ActualLSGOriginalPrimeFibres318
public section
noncomputable section

namespace ActualGaussianWeberOriginalAbscissaHeight318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberOddOrdinate318 ActualGaussianWeberEvenAbscissa318
open ActualGaussianWeberComplexFibreSeed318 ActualGaussianWeberComplexFibreDegree318
open ActualGaussianWeberOneComplexFibre318 ActualLSGOriginalPrimeFibres318

attribute [local instance] Classical.decEq

/-- This is the original integral Gaussian i in the coefficient field,
not an arbitrary quadratic root chosen after complex base change. -/
@[expose] def originalI : Base := algebraMap GaussianInt Base gaussianI

theorem originalI_sq : originalI^2 = -1 := by
  simpa only [originalI,map_pow,map_neg,map_one] using
    congrArg (algebraMap GaussianInt Base) gaussianI_sq

theorem base_two_ne : (2:Base) ≠ 0 := by
  intro h
  have e := congrArg complexEmbedding h
  exact (by norm_num : (2:ℂ) ≠ 0) (by simpa only [map_ofNat,map_zero] using e)

private theorem finite_stock_image {k : Type*} [Field k] (P : WP k) (hP : P ≠ 0) :
    ∃ x y : k, ∃ h : (curve k).toAffine.Nonsingular x y, P = Point.some x y h := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h => exact ⟨x,y,h,rfl⟩

private theorem same_scalar {i j : ℂ} (hi : i^2 = -1) (hj : j^2 = -1)
    (e : i = j) (a b : ℤ) (hC : (2:ℂ) ≠ 0) :
    gaussian hC i hi a b = gaussian hC j hj a b := by
  subst j
  rfl

/-- Exact characteristic-zero abscissa height of the same signed
prime-norm Gaussian scalar. The complex fibre size is the actual
strict positive-i theorem, not a premise. Both degrees are capped. -/
theorem original_abscissa_height_at_most_prime
    (p : ℕ) (hp : p.Prime) (hOdd : Odd (p:ℤ)) (a b : ℤ) (hN : a^2+b^2=(p:ℤ)) :
    ∃ u v : FunctionField Base, ∃ h : (curve (FunctionField Base)).toAffine.Nonsingular u v,
      gaussian (function_two_ne Base base_two_ne) (constGeneric Base originalI)
        (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric Base) originalI_sq)
        a b (genericPoint Base base_two_ne) = Point.some u v h ∧
      ∃ r : RatFunc Base, IsCoprime r.num r.denom ∧ r.denom ≠ 0 ∧
        u = polyFrac Base r.num / polyFrac Base r.denom ∧
        max r.num.natDegree r.denom.natDegree ≤ p := by
  have hNon := odd_generic_nonorigin Base base_two_ne originalI originalI_sq a b (p:ℤ) hN hOdd
  obtain ⟨u,v,huv,hGen⟩ := finite_stock_image _ hNon
  obtain ⟨r,hAB,hB,hRat⟩ := scalar_actual_x_ratio Base base_two_ne originalI originalI_sq
    a b u v huv hGen
  have hSurj : Function.Surjective (fun z : ℤ×ℤ => (⟨z.1,z.2⟩ : GaussianInt)) := by
    rintro ⟨x,y⟩
    exact ⟨(x,y),rfl⟩
  letI : Countable GaussianInt := hSurj.countable
  letI : Countable Base := fraction_countable GaussianInt Base
  letI : Algebra Base ℂ := complexEmbedding.toAlgebra
  let hC : (2:ℂ) ≠ 0 := by norm_num
  let f := algebraMap Base ℂ
  have hiC : (f originalI)^2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg f originalI_sq
  have hfI : f originalI = Complex.I := by
    change complexEmbedding (algebraMap GaussianInt Base gaussianI) = Complex.I
    exact complexEmbedding_i
  have hFib : ∀ Q : WP ℂ,
      Finite {P : WP ℂ // gaussian hC (f originalI) hiC a b P = Q} ∧
        Nat.card {P : WP ℂ // gaussian hC (f originalI) hiC a b P = Q} = p := by
    rw [same_scalar hiC Complex.I_sq hfI a b hC]
    exact original_complex_prime_fibres p hp a b hN
  have hRat' : u = fractionMap Base (AdjoinRoot.of (relation Base) r.num) /
        fractionMap Base (AdjoinRoot.of (relation Base) r.denom) := hRat
  obtain ⟨c,hc⟩ := exists_transcendental_complex (K:=Base)
  obtain ⟨_,_,_,hCard⟩ := roots_embed_and_card_le base_two_ne hC originalI originalI_sq
    a b r.num r.denom hAB u v huv hGen hRat' c hc p hFib
  have hCap := (full_distinct_root_card r.num r.denom hAB hB c hc).symm.trans_le hCard
  exact ⟨u,v,huv,hGen,r,hAB,hB,hRat,hCap⟩

end ActualGaussianWeberOriginalAbscissaHeight318
