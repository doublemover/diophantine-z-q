module
public import IntegralInfinityCoefficients318
public import ReciprocalInfinityNormalization318
public section
noncomputable section
namespace IntegralInfinityOriginalField318
open Polynomial
attribute [-instance] DivisionRing.toRatAlgebra
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Common literal presentation, so coefficient equality induces the actual
ring comparison, including polynomial-coordinate maps. -/
abbrev Presentation (a : Fin 3 → ℚ[X]) :=
  ThreeRootOrder318.Order (fun j =>
    algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3, a k)) (a j))
@[expose] def presentationEquiv {a b : Fin 3 → ℚ[X]} (h : a = b) :
    Presentation a ≃ₐ[ℚ] Presentation b := by
  subst b
  exact AlgEquiv.refl
theorem presentationEquiv_polynomial {a b : Fin 3 → ℚ[X]} (h : a = b) (p : ℚ[X]) :
    presentationEquiv h (algebraMap ℚ[X] (Presentation a) p) =
      algebraMap ℚ[X] (Presentation b) p := by
  subst b
  rfl

variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (InfinityFieldCoordinates318.L c) :=
  (KummerTensorField318.source_raw_field c).toField
/-- The rational specialization is the already-constructed original infinity
order, not only a degree-eight algebra with matching numerical invariants. -/
@[expose] def rationalOrderEquiv :
    IntegralInfinityChart318.Order ℚ c ≃ₐ[ℚ] InfinityOpenChart318.OpenOrder c :=
  presentationEquiv (funext (IntegralInfinityCoefficients318.rational_coefficient c))

theorem rationalOrderEquiv_polynomial (p : ℚ[X]) :
    rationalOrderEquiv c (algebraMap ℚ[X] (IntegralInfinityChart318.Order ℚ c) p) =
      algebraMap ℚ[X] (InfinityOpenChart318.OpenOrder c) p :=
  presentationEquiv_polynomial (funext (IntegralInfinityCoefficients318.rational_coefficient c)) p

/-- An actual embedding into the same original four-contact function field. -/
@[expose] def originalEmbedding :
    IntegralInfinityChart318.Order ℚ c →+* InfinityFieldCoordinates318.L c :=
  (InfinityOpenFractionField318.openEmbedding c).comp (rationalOrderEquiv c).toRingHom

theorem originalEmbedding_injective : Function.Injective (originalEmbedding c) :=
  (InfinityOpenFractionField318.openEmbedding_injective c).comp (rationalOrderEquiv c).injective

theorem original_coordinate :
    originalEmbedding c (IntegralInfinityChart318.coordinate ℚ c) = InfinityFieldCoordinates318.u c := by
  unfold originalEmbedding
  rw [RingHom.comp_apply]
  change InfinityOpenFractionField318.openEmbedding c (rationalOrderEquiv c
    (algebraMap ℚ[X] (IntegralInfinityChart318.Order ℚ c) X)) = _
  rw [rationalOrderEquiv_polynomial]
  change InfinityOpenFractionField318.openEmbedding c
    (algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c)
      (algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) X)) = _
  rw [ReciprocalInfinityNormalization318.openEmbedding_on_polynomial,Polynomial.aeval_X]

/-- The verified coordinate is literally c0/y0 in that original field. -/
theorem original_coordinate_formula :
    originalEmbedding c (IntegralInfinityChart318.coordinate ℚ c) =
      algebraMap ℚ (InfinityFieldCoordinates318.L c) (c 0 : ℚ) / InfinityFieldCoordinates318.root c 0 := by
  rw [original_coordinate]
  rfl

theorem rational_domain : IsDomain (IntegralInfinityChart318.Order ℚ c) :=
  Function.Injective.isDomain (originalEmbedding c) (originalEmbedding_injective c)

/-- The reciprocal expression recovers the same original t coordinate. -/
theorem recover_original_t :
    algebraMap ℚ (InfinityFieldCoordinates318.L c) (c 0 : ℚ) /
      originalEmbedding c (IntegralInfinityChart318.coordinate ℚ c)^2 =
        InfinityFieldCoordinates318.t c := by
  rw [original_coordinate]
  exact (InfinityFieldCoordinates318.recover_t c).symm

end IntegralInfinityOriginalField318
