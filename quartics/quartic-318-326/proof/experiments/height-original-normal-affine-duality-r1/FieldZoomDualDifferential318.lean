module
public import FiniteDualDifferentialRealization318
public import FieldContactZoomTensor318
public import NormalizedDualBicanonicalSections318
public section
noncomputable section
namespace FieldZoomDualDifferential318
open Polynomial IntegralContactZoomCoefficients318
open FiniteDualTransport318 FiniteDualDifferentialRealization318
open scoped TensorProduct
set_option maxHeartbeats 2400000
variable {K : Type*} [Field K] [CharZero K] (d a : Fin 4 → K) (t : K) (m : Mode)
  (y : Fin 4 → K)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,y i≠0)

@[expose] def parameter : Fin 4 → K[X] := match m with
  | .finite => DVRNormalizedFiniteOrder318.coefficient K d a
  | .reciprocal => DVRNormalizedInfinityOrder318.coefficient K d a
abbrev Order := FourRootOrder318.Order (parameter d a m)
@[expose] def scalarMap : K[X] →+* Chart d a t m :=
  Polynomial.eval₂RingHom (algebraMap K _) (oldCoordinate d a t m)

include hy in
lemma root_relation (i : Fin 4) :
    (IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y i)^2=
      scalarMap d a t m (parameter d a m i) := by
  rw [original_root_square d a t m y hy]
  cases m <;> simp only [scalarMap,parameter,DVRNormalizedFiniteOrder318.coefficient,
    DVRNormalizedInfinityOrder318.coefficient,coe_eval₂RingHom,eval₂_mul,eval₂_sub,
    eval₂_C,eval₂_X,eval₂_one,contactFactor,mul_one]

/-- The literal whole normalized order map, with its original coordinate
and every signed normalized root. -/
@[expose] def sourceMap : Order d a m →+* Chart d a t m := by
  letI : Algebra K[X] (Chart d a t m) := (scalarMap d a t m).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (parameter d a m)
    (IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y)
    (root_relation d a t m y hy)).toRingHom

theorem sourceMap_polynomial (p : K[X]) : sourceMap d a t m y hy
    (algebraMap K[X] (Order d a m) p)=scalarMap d a t m p := by
  letI : Algebra K[X] (Chart d a t m) := (scalarMap d a t m).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ _ (root_relation d a t m y hy)).commutes p

theorem sourceMap_root (i : Fin 4) : sourceMap d a t m y hy
    (FourRootOrderSigns318.generator (parameter d a m) i)=
      IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y i := by
  letI : Algebra K[X] (Chart d a t m) := (scalarMap d a t m).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

@[expose] def different : (Chart d a t m)ˣ :=
  ((IsUnit.mk0 (16:K) (by norm_num)).map (algebraMap K _)).unit *
    (FieldContactZoomTensor318.original_product_unit d a t m y hn).unit

theorem different_value : (different d a t m y hn:Chart d a t m)=
    16*∏ i : Fin 4,IntegralZoomNeighborhood318.oldRoot K (alpha d a m) d (gamma d a m) t y i := by
  simp [different,Units.val_mul,IsUnit.unit_spec]

include hy in
theorem different_square : (different d a t m y hn:Chart d a t m)^2=
    algebraMap K _ (256*∏ i : Fin 4,d i)*weight d a t m*contactProduct d a t m := by
  rw [different_value,mul_pow,original_product_square d a t m y hy]
  simp only [map_mul,map_ofNat]
  ring

/-- Actual generic differential represented by the model finite-dual
highest-root generator and its base coordinate differential. -/
@[expose] def omega : Omega d a t m :=
  (↑(different d a t m y hn)⁻¹:Chart d a t m) •
    KaehlerDifferential.D K _ (oldCoordinate d a t m)

@[expose] def realization : Square (R:=K[X]) (A:=Order d a m) →ₛₗ[sourceMap d a t m y hy]
    Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  FiniteDualDifferentialRealization318.squareRealization
    (FourRootIntegralDuality318.frame (parameter d a m))
      (sourceMap d a t m y hy) (omega d a t m y hn)

include hy in
/-- Exact cancellation of the ACTUAL generic different, before any
point specialization, retaining the integral twist product and reciprocal weight. -/
theorem coefficient_cancellation : contactProduct d a t m*
    (algebraMap K _ (256*∏ i : Fin 4,d i)*weight d a t m)*
      (↑(different d a t m y hn)⁻¹:Chart d a t m)^2=1 := by
  calc
    _ = (different d a t m y hn:Chart d a t m)^2*
        (↑(different d a t m y hn)⁻¹:Chart d a t m)^2 := by rw [different_square d a t m y hy hn]; ring
    _ = _ := by rw [←mul_pow,Units.mul_inv,one_pow]

include hy in
theorem normalized_q0 : section0 d a t m=
    (algebraMap K _ (256*∏ i : Fin 4,d i)*weight d a t m) •
      (omega d a t m y hn ⊗ₜ[Chart d a t m] omega d a t m y hn) := by
  apply FieldContactZoomTensor318.q0_unique d a t m y hy hn
  rw [omega,TensorProduct.smul_tmul_smul,smul_smul,smul_smul]
  have hc := coefficient_cancellation d a t m y hy hn
  simpa only [pow_two,one_smul,mul_assoc] using congrArg
    (fun r : Chart d a t m => r • (KaehlerDifferential.D K _ (oldCoordinate d a t m) ⊗ₜ[Chart d a t m]
      KaehlerDifferential.D K _ (oldCoordinate d a t m))) hc
end FieldZoomDualDifferential318
