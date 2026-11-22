module
public import ActualGaussianWeberPositivePeriodAnnihilator318
public import ActualGaussianWeberIntegerModel318
public section
noncomputable section

namespace ActualGaussianWeberArithmeticPeriodPrimitive318

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberQuarterTurn318 ActualGaussianWeberIntegerModel318
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberComplexUniformizationFibres318
open ActualGaussianWeberOriginalFieldFoundation318 ActualGaussianWeberFullCoordinateField318
open ActualGaussianWeberAlgebraicClosureTorsion318 ActualGaussianWeberPositivePeriodAnnihilator318

attribute [local instance] Classical.decEq

local notation "Dₘ[" M "]" => ↥(fullField Ω M)

private theorem scalar_pair (c d : ℤ) (q : Torus) :
    scalar (literal c d) q=c • q+d • scalar gaussianI q := by
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective lattice q
  have hi : iota gaussianI=Complex.I := by
    change (((⟨0,1⟩ : GaussianInt):ℂ))=Complex.I
    rw [GaussianInt.toComplex_def'] <;> simp
  rw [scalar_on,scalar_on,hi,←map_zsmul,←map_zsmul,←map_add]
  have he : iota (literal c d)=(c:ℂ)+(d:ℂ)*Complex.I := by
    change (((⟨c,d⟩:GaussianInt):ℂ))=_
    exact GaussianInt.toComplex_def' c d
  apply congrArg V
  rw [he,zsmul_eq_mul,zsmul_eq_mul] <;> ring

/-- Gaussian primitivity of the same proposed positive period point
in the original full field. The quarter-turn uses exactly the
selected valuation's original integral Gaussian generator, not an
arbitrary square root, and the comparison uses the old closure
embedding. No assertion about other points or a module basis. -/
theorem old_positive_period_point_gaussian_primitive
    (M : ℕ) (hM : 1<M) [NumberField (Dₘ[M])]
    (w : HeightOneSpectrum (𝓞 (Dₘ[M]))) (P : WP (Dₘ[M]))
    (hImage : coordinateHom (chosenClosureEmbedding.comp (algebraMap (Dₘ[M]) Ω))
      (by norm_num : (2:ℂ)≠0) P =
        ActualLSGOriginalFullUniformization318.uniformization.point (V ((1:ℂ)/(M:ℂ)))) :
    letI := integralAlgebra (algebraMap Base (Dₘ[M]))
    let W := OverPlace (L:=Dₘ[M]) w
    let i := integralOverI (L:=Dₘ[M]) w
    let hi := integralOverI_sq (L:=Dₘ[M]) w
    ∀ c d : ℤ, c • P+d • turn (by norm_num : (2:(Dₘ[M]))≠0) (W.subtype i)
      (chosen_square_generic W i hi) P=0 → (M:ℤ)∣c ∧ (M:ℤ)∣d := by
  letI := integralAlgebra (algebraMap Base (Dₘ[M]))
  let W := OverPlace (L:=Dₘ[M]) w
  let i : W := integralOverI (L:=Dₘ[M]) w
  let hi : i^2= -1 := integralOverI_sq (L:=Dₘ[M]) w
  let iL := W.subtype i
  let hiL := chosen_square_generic W i hi
  let hL : (2:(Dₘ[M]))≠0 := by norm_num
  let hC : (2:ℂ)≠0 := by norm_num
  let f : (Dₘ[M])→+*ℂ :=
    chosenClosureEmbedding.comp (algebraMap (Dₘ[M]) Ω)
  let E := coordinateHom f hC
  let U := ActualLSGOriginalFullUniformization318.uniformization
  let q := V ((1:ℂ)/(M:ℂ))
  have hIm : E P=U.point q := hImage
  have hInt : iL=algebraMap Base (Dₘ[M]) (algebraMap GaussianInt Base gaussianI) := by
    change algebraMap W (Dₘ[M])
      (algebraMap (𝓞 (Dₘ[M])) W (integralEmbedding (algebraMap Base (Dₘ[M])) gaussianI))=_
    rw [←IsScalarTower.algebraMap_apply (𝓞 (Dₘ[M])) W (Dₘ[M]),integral_to_field]
  have hSign : f iL=Complex.I := by
    rw [hInt]
    change chosenClosureEmbedding
      (algebraMap (Dₘ[M]) Ω (algebraMap Base (Dₘ[M]) (algebraMap GaussianInt Base gaussianI)))=_
    rw [←IsScalarTower.algebraMap_apply Base (Dₘ[M]) Ω]
    exact chosen_closure_positive_I
  change ∀ c d : ℤ, c • P+d • turn hL iL hiL P=0 → (M:ℤ)∣c ∧ (M:ℤ)∣d
  intro c d h
  have hZero : gaussian hL iL hiL c d P=0 := h
  have hComm : E (gaussian hL iL hiL c d P)=
      gaussian hC Complex.I Complex.I_sq c d (E P) :=
    coordinate_gaussian f hL hC iL Complex.I hiL Complex.I_sq hSign c d P
  rw [hZero,map_zero,hIm] at hComm
  have hU : U.point (scalar (literal c d) q)=
      gaussian hC Complex.I Complex.I_sq c d (U.point q) := by
    rw [scalar_pair,map_add,map_zsmul,map_zsmul,U.quarter] <;> rfl
  have hKernel : scalar (literal c d) q=0 :=
    U.point.injective (hU.trans (hComm.symm.trans (map_zero U.point).symm))
  obtain ⟨z,hz⟩ :=
    (literal_positive_period_annihilator M (Nat.zero_lt_one.trans hM) (literal c d)).mp hKernel
  refine ⟨⟨z.re,?_⟩,⟨z.im,?_⟩⟩
  · simpa only [literal,Zsqrtd.re_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
      mul_zero,zero_mul,add_zero] using congrArg (fun x : GaussianInt => x.re) hz
  · simpa only [literal,Zsqrtd.im_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
      mul_zero,zero_mul,zero_add,add_zero] using congrArg (fun x : GaussianInt => x.im) hz

end ActualGaussianWeberArithmeticPeriodPrimitive318
