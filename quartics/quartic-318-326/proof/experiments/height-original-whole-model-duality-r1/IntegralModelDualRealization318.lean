module
public import FieldZoomModelSections318
public import OriginalAllPrimeIntegralBicanonical318
public section
noncomputable section
namespace IntegralModelDualRealization318
open Polynomial IntegralContactZoomCoefficients318 IntegralContactZoomBaseChange318
open FiniteDualTransport318
open scoped TensorProduct
set_option maxHeartbeats 2600000
variable {V K : Type*} [CommRing V] [Field K] [CharZero K] [Algebra V K]
  (d a : Fin 4 → V) (t : V) (m : Mode) (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,algebraMap V K (y i)≠0)
local notation "dK" => mapped (S:=K) d
local notation "aK" => mapped (S:=K) a
local notation "tK" => algebraMap V K t
local notation "yK" => mapped (S:=K) y
local notation "B" => Changed (S:=K) d a t m
@[expose] def parameter : Fin 4 → V[X] := match m with
  | .finite => DVRNormalizedFiniteOrder318.coefficient V d a
  | .reciprocal => DVRNormalizedInfinityOrder318.coefficient V d a
abbrev Order := FourRootOrder318.Order (parameter d a m)
@[expose] def scalarMap : V[X] →+* B :=
  Polynomial.eval₂RingHom (algebraMap V B) (oldCoordinate dK aK tK m)
@[expose] def root (i : Fin 4) : B :=
  IntegralZoomNeighborhood318.oldRoot K (alpha dK aK m) dK (gamma dK aK m) tK yK i

include hy in
lemma root_relation (i : Fin 4) : (root (K:=K) d a t m y i)^2=
    scalarMap (K:=K) d a t m (parameter d a m i) := by
  rw [root,original_root_square dK aK tK m yK (mapped_root_equation d a t m y hy)]
  cases m <;> simp only [scalarMap,parameter,DVRNormalizedFiniteOrder318.coefficient,
    DVRNormalizedInfinityOrder318.coefficient,coe_eval₂RingHom,eval₂_mul,eval₂_sub,
    eval₂_C,eval₂_X,eval₂_one,contactFactor,mul_one,mapped,
    ←IsScalarTower.algebraMap_apply V K]

/-- Whole integral model map into its actual generic smooth neighborhood,
including the polynomial scalar map and EVERY original normalized root. -/
@[expose] def sourceMap : Order d a m →+* B := by
  letI : Algebra V[X] B := (scalarMap (K:=K) d a t m).toAlgebra
  exact (IntegralRootPointMaps318.fourMap (parameter d a m) (root (K:=K) d a t m y)
    (root_relation d a t m y hy)).toRingHom

theorem sourceMap_polynomial (p : V[X]) : sourceMap (K:=K) d a t m y hy
    (algebraMap V[X] (Order d a m) p)=scalarMap (K:=K) d a t m p := by
  letI : Algebra V[X] B := (scalarMap (K:=K) d a t m).toAlgebra
  exact (IntegralRootPointMaps318.fourMap _ _ (root_relation d a t m y hy)).commutes p

theorem sourceMap_root (i : Fin 4) : sourceMap (K:=K) d a t m y hy
    (FourRootOrderSigns318.generator (parameter d a m) i)=root (K:=K) d a t m y i := by
  letI : Algebra V[X] B := (scalarMap (K:=K) d a t m).toAlgebra
  exact IntegralRootPointMaps318.fourMap_generator _ _ _ i

@[expose] def realization : Square (R:=V[X]) (A:=Order d a m) →ₛₗ[sourceMap (K:=K) d a t m y hy]
    Omega dK aK tK m ⊗[B] Omega dK aK tK m :=
  FiniteDualDifferentialRealization318.squareRealization
    (FourRootIntegralDuality318.frame (parameter d a m))
    (sourceMap (K:=K) d a t m y hy) (FieldZoomDualDifferential318.omega dK aK tK m yK hn)

@[expose] def polynomial0 : V[X] := match m with
  | .finite => NormalizedDualBicanonicalSections318.finite0 V d
  | .reciprocal => NormalizedDualBicanonicalSections318.infinity0 V d
@[expose] def polynomial1 : V[X] := match m with
  | .finite => NormalizedDualBicanonicalSections318.finite1 V d
  | .reciprocal => NormalizedDualBicanonicalSections318.infinity1 V d
@[expose] def modelSection (p : V[X]) : Square (R:=V[X]) (A:=Order d a m) :=
  squareFrame (FourRootIntegralDuality318.frame (parameter d a m)) (algebraMap V[X] (Order d a m) p)

lemma polynomial0_value : scalarMap (K:=K) d a t m (polynomial0 d m)=
    FieldZoomDualDifferential318.scalarMap dK aK tK m (FieldZoomModelSections318.polynomial0 dK m) := by
  cases m <;> simp [scalarMap,FieldZoomDualDifferential318.scalarMap,
    polynomial0,FieldZoomModelSections318.polynomial0,NormalizedDualBicanonicalSections318.finite0,
    NormalizedDualBicanonicalSections318.infinity0,NormalizedDualBicanonicalSections318.constant,
    mapped,←IsScalarTower.algebraMap_apply V K B,←map_prod]

lemma polynomial1_value : scalarMap (K:=K) d a t m (polynomial1 d m)=
    FieldZoomDualDifferential318.scalarMap dK aK tK m (FieldZoomModelSections318.polynomial1 dK m) := by
  cases m <;> simp [scalarMap,FieldZoomDualDifferential318.scalarMap,
    polynomial1,FieldZoomModelSections318.polynomial1,NormalizedDualBicanonicalSections318.finite1,
    NormalizedDualBicanonicalSections318.infinity1,NormalizedDualBicanonicalSections318.constant,
    mapped,←IsScalarTower.algebraMap_apply V K B,←map_prod]

theorem section0_image : realization (K:=K) d a t m y hy hn
    (modelSection d a m (polynomial0 d m))=section0 dK aK tK m := by
  rw [realization,modelSection,FiniteDualDifferentialRealization318.squareRealization_frame,
    sourceMap_polynomial,polynomial0_value]
  rw [←FieldZoomModelSections318.realization_modelSection dK aK tK m yK
    (mapped_root_equation d a t m y hy) hn]
  exact FieldZoomModelSections318.section0_image dK aK tK m yK
    (mapped_root_equation d a t m y hy) hn

theorem section1_image : realization (K:=K) d a t m y hy hn
    (modelSection d a m (polynomial1 d m))=section1 dK aK tK m := by
  rw [realization,modelSection,FiniteDualDifferentialRealization318.squareRealization_frame,
    sourceMap_polynomial,polynomial1_value]
  rw [←FieldZoomModelSections318.realization_modelSection dK aK tK m yK
    (mapped_root_equation d a t m y hy) hn]
  exact FieldZoomModelSections318.section1_image dK aK tK m yK
    (mapped_root_equation d a t m y hy) hn
end IntegralModelDualRealization318
