module
public import FieldZoomDualDifferential318
public section
noncomputable section
namespace FieldZoomModelSections318
open Polynomial IntegralContactZoomCoefficients318
open FieldZoomDualDifferential318 FiniteDualTransport318
open scoped TensorProduct
set_option maxHeartbeats 2400000
variable {K : Type*} [Field K] [CharZero K] (d a : Fin 4 → K) (t : K) (m : Mode)
  (y : Fin 4 → K)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,y i≠0)

@[expose] def polynomial0 : K[X] := match m with
  | .finite => NormalizedDualBicanonicalSections318.finite0 K d
  | .reciprocal => NormalizedDualBicanonicalSections318.infinity0 K d
@[expose] def polynomial1 : K[X] := match m with
  | .finite => NormalizedDualBicanonicalSections318.finite1 K d
  | .reciprocal => NormalizedDualBicanonicalSections318.infinity1 K d
@[expose] def modelSection (p : K[X]) : Square (R:=K[X]) (A:=Order d a m) :=
  squareFrame (FourRootIntegralDuality318.frame (parameter d a m))
    (algebraMap K[X] (Order d a m) p)

lemma realization_modelSection (p : K[X]) :
    realization d a t m y hy hn (modelSection d a m p)=
      scalarMap d a t m p • (omega d a t m y hn ⊗ₜ[Chart d a t m] omega d a t m y hn) := by
  rw [realization,modelSection,FiniteDualDifferentialRealization318.squareRealization_frame,
    sourceMap_polynomial]

lemma polynomial0_value : scalarMap d a t m (polynomial0 d m)=
    algebraMap K _ (256*∏ i : Fin 4,d i)*weight d a t m := by
  cases m <;> simp [scalarMap,polynomial0,NormalizedDualBicanonicalSections318.finite0,
    NormalizedDualBicanonicalSections318.infinity0,NormalizedDualBicanonicalSections318.sectionCoefficient,
    weight]

/-- The genuine model-dual tensor section maps to the SAME original
integral zoom section on the generic fiber, not merely to its value. -/
theorem section0_image : realization d a t m y hy hn
    (modelSection d a m (polynomial0 d m))=section0 d a t m := by
  rw [realization_modelSection,polynomial0_value,←normalized_q0 d a t m y hy hn]

include hn in
lemma reciprocal_coordinate_unit
    (hyR : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value
      (alpha d a .reciprocal) d (gamma d a .reciprocal) t i) : IsUnit (oldCoordinate d a t .reciprocal) := by
  have hu := (FieldContactZoomTensor318.original_root_unit d a t .reciprocal y hn 0).pow 2
  rw [original_root_square d a t .reciprocal y hyR] at hu
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)

/-- The second section retains its actual finite power1/reciprocal
power3 coefficient and the exact full-tensor relation to the first. -/
theorem section1_image : realization d a t m y hy hn
    (modelSection d a m (polynomial1 d m))=section1 d a t m := by
  cases m with
  | finite =>
    rw [realization_modelSection,finite_section_ratio,normalized_q0 d a t .finite y hy hn]
    simp only [scalarMap,polynomial1,NormalizedDualBicanonicalSections318.finite1,
      NormalizedDualBicanonicalSections318.sectionCoefficient,coe_eval₂RingHom,eval₂_mul,
      eval₂_X,eval₂_C,weight,mul_one,smul_smul]
  | reciprocal =>
    apply (reciprocal_coordinate_unit d a t y hn hy).smul_left_cancel.mp
    rw [reciprocal_section_ratio,realization_modelSection,normalized_q0 d a t .reciprocal y hy hn]
    simp only [scalarMap,polynomial1,NormalizedDualBicanonicalSections318.infinity1,
      NormalizedDualBicanonicalSections318.sectionCoefficient,coe_eval₂RingHom,eval₂_mul,
      eval₂_X,eval₂_C,eval₂_pow,weight,smul_smul]
    congr 1
    ring
end FieldZoomModelSections318
