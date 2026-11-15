module
public import PELIntegralPeriodKernel318
public import PELPrimeLatticeCokernel318
public section
noncomputable section
namespace PELPrimePeriodIsogenies318
open QuaternionicRealPeriod318 PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELQuaternionRealRepresentation318 PELComplexPeriodSurface318 PELPrimeNormalizerData318
open PELPositiveNormPeriodMap318 PELIntegralPeriodKernel318
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000

/-- The exact four original integral normalizers, not newly chosen elements
of the same norm or a rationally equivalent replacement lattice. -/
@[expose] def primeElement (i : Fin 4) : order := coordinatesEquiv (coefficients i)

theorem primeElement_value (i : Fin 4) : (primeElement i:B)=element i :=
  coordinatesEquiv_value (coefficients i)

theorem primeElement_norm (i : Fin 4) : reducedNorm (primeElement i:B)=prime i := by
  rw [primeElement_value,element_norm]

theorem primeElement_positive (i : Fin 4) : 0<reducedNorm (primeElement i:B) := by
  rw [primeElement_norm]
  exact prime_positive i

theorem exact_rightMultiply (i : Fin 4) :
    PELIntegralPeriodKernel318.rightMultiply (primeElement i)=
      PELPrimeLatticeResidues318.rightMultiply i := rfl

@[expose] def cokernelComparison (i : Fin 4) :
    (order ⧸ (PELIntegralPeriodKernel318.rightMultiply (primeElement i)).range) ≃+
      PELPrimeLatticeCokernel318.Cokernel i :=
  QuotientAddGroup.quotientAddEquivOfEq (congrArg AddMonoidHom.range (exact_rightMultiply i))

variable (i : Fin 4) (τ : ℂ) (hτ : 0<τ.im)
@[expose] def primeMap : Surface (translated (primeElement i) τ) →+ Surface τ :=
  originalMap (primeElement i) (primeElement_positive i) τ hτ

/-- The actual analytic kernel, not only the original lattice cokernel,
is the specified two-dimensional residue group for each prime normalizer. -/
@[expose] def primeKernelEquiv : (primeMap i τ hτ).ker ≃+ (Fin 2 → ZMod (prime i)) :=
  (kernelEquiv (primeElement i) (primeElement_positive i) τ hτ).symm.trans
    ((cokernelComparison i).trans (PELPrimeLatticeCokernel318.quotientEquiv i))

noncomputable instance primeKernelFintype : Fintype (primeMap i τ hτ).ker :=
  Fintype.ofEquiv (Fin 2 → ZMod (prime i)) (primeKernelEquiv i τ hτ).symm.toEquiv

theorem prime_kernel_card : Fintype.card (primeMap i τ hτ).ker=(prime i)^2 := by
  rw [Fintype.card_congr (primeKernelEquiv i τ hτ).toEquiv]
  simp

theorem primeMap_surjective : Function.Surjective (primeMap i τ hτ) :=
  originalMap_surjective (primeElement i) (primeElement_positive i) τ hτ

theorem primeMap_holomorphic :
    letI := surfaceCharts (translated (primeElement i) τ)
      (translated_positive (primeElement i) (primeElement_positive i) τ hτ)
    letI := surfaceCharts τ hτ
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (primeMap i τ hτ) :=
  originalMap_holomorphic (primeElement i) (primeElement_positive i) τ hτ

/-- The original principal positive form has multiplier p, while the
actual analytic kernel has order p². These are deliberately different quantities. -/
theorem prime_polarization_multiplier (z w : ComplexVectors) :
    PELPeriodRiemannForm318.riemann τ hτ
      (QuaternionicIntegralPeriodMap318.periodScalar representation order (primeElement i) τ z)
      (QuaternionicIntegralPeriodMap318.periodScalar representation order (primeElement i) τ w)=
    (prime i:ℝ)*PELPeriodRiemannForm318.riemann (translated (primeElement i) τ)
      (translated_positive (primeElement i) (primeElement_positive i) τ hτ) z w := by
  have h := polarization_multiplier (primeElement i) (primeElement_positive i) τ hτ z w
  simpa only [primeElement_norm,Rat.cast_natCast] using h

/-- All four original prime normalizers are included, with every actual
upper-half-plane parameter retained. No algebraic degree is inferred here. -/
theorem literal_kernel_orders :
    Fintype.card (primeMap 0 τ hτ).ker=4 ∧ Fintype.card (primeMap 1 τ hτ).ker=9 ∧
    Fintype.card (primeMap 2 τ hτ).ker=25 ∧ Fintype.card (primeMap 3 τ hτ).ker=49 := by
  simp [prime_kernel_card,prime]
end PELPrimePeriodIsogenies318
