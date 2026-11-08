module
public import ReciprocalInfinityBase318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace ReciprocalInfinityNormalization318
open Polynomial
open scoped TensorProduct
open InfinityOpenChart318 ReciprocalInfinityBase318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=InfinityFieldCoordinates318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance openDomain : IsDomain (OpenOrder c):=openOrder_domain c

/-- Compatibility of the actual unlocalized order embedding with every
polynomial in its infinity coordinate. -/
theorem originalEmbedding_on_polynomial (p:R) :
    InfinityFractionField318.originalEmbedding c (algebraMap R (Order c) p)=
      Polynomial.aeval (InfinityFieldCoordinates318.u c) p := by
  have h : embedding c (algebraMap R (Order c) p)=
      algebraMap K (InfinityFieldEquivalence318.B c) (algebraMap R K p) := by
    unfold embedding
    simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom,AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R K (K⊗[R]Order c)]
    exact (genericFiber c).commutes _
  change InfinityFieldEquivalence318.fieldEquiv c (embedding c (algebraMap R (Order c) p))=_
  rw [h,InfinityFieldEquivalence318.fieldEquiv_on_coordinate,
    InfinityFieldMap318.coordinateField_on_polynomial]

theorem orderToOpen_on_polynomial (p:R) :
    InfinityOpenFractionField318.orderToOpen c (algebraMap R (Order c) p)=
      algebraMap (OpenBase c) (OpenOrder c) (algebraMap R (OpenBase c) p) := by
  unfold InfinityOpenFractionField318.orderToOpen
  simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R (OpenBase c) (OpenBase c⊗[R]Order c)]
  exact (openBaseChange c).commutes _

theorem openEmbedding_on_polynomial (p:R) :
    InfinityOpenFractionField318.openEmbedding c
      (algebraMap (OpenBase c) (OpenOrder c) (algebraMap R (OpenBase c) p))=
        Polynomial.aeval (InfinityFieldCoordinates318.u c) p := by
  rw [←orderToOpen_on_polynomial,InfinityOpenFractionField318.openEmbedding_on_order,
    originalEmbedding_on_polynomial]

@[expose] def reciprocalEmbedding : ReciprocalOpen c→+*L c:=
  (InfinityOpenFractionField318.openEmbedding c).comp (chartMap c)

/-- The reciprocal coordinate really maps to the inverse of the original
contact coordinate t, not merely to an abstract degree-two parameter. -/
theorem reciprocalEmbedding_coordinate :
    reciprocalEmbedding c (algebraMap R (ReciprocalOpen c) X)=
      (InfinityFieldCoordinates318.t c)⁻¹ := by
  unfold reciprocalEmbedding chartMap openMap
  simp only [RingHom.comp_apply,IsLocalization.Away.map,IsLocalization.map_eq]
  rw [substitution_X,openEmbedding_on_polynomial]
  simp only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
  exact (InfinityFieldCoordinates318.reciprocal_contact_square c).symm

local instance chartAlgebra : Algebra (ReciprocalOpen c) (OpenOrder c):=(chartMap c).toAlgebra
local instance chartSMul : SMul (ReciprocalOpen c) (OpenOrder c):=(chartAlgebra c).toSMul
local instance chartModule : Module (ReciprocalOpen c) (OpenOrder c):=Algebra.toModule
local instance chartFinite : Module.Finite (ReciprocalOpen c) (OpenOrder c):=chartMap_finite c
local instance openOriginalAlgebra : Algebra (OpenOrder c) (L c):=
  (InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance originalFraction : IsFractionRing (OpenOrder c) (L c):=
  InfinityOpenFractionField318.open_fractionField c
local instance reciprocalAlgebra : Algebra (ReciprocalOpen c) (L c):=(reciprocalEmbedding c).toAlgebra
local instance reciprocalSMul : SMul (ReciprocalOpen c) (L c):=(reciprocalAlgebra c).toSMul
local instance reciprocalModule : Module (ReciprocalOpen c) (L c):=Algebra.toModule
local instance originalTower : IsScalarTower (ReciprocalOpen c) (OpenOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=ReciprocalOpen c) (S:=OpenOrder c) (A:=L c) (fun _=>rfl)
local instance selfTower : IsScalarTower (ReciprocalOpen c) (ReciprocalOpen c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=ReciprocalOpen c) (S:=ReciprocalOpen c) (A:=L c) (fun _=>rfl)

/-- The explicit infinity neighborhood is exactly the integral closure of
the reciprocal projective-line open inside the original contact field. -/
theorem actual_integralClosure : IsIntegralClosure (OpenOrder c) (ReciprocalOpen c) (L c) := by
  let :=InfinityNormalChart318.open_integrallyClosed c
  constructor
  · exact InfinityOpenFractionField318.openEmbedding_injective c
  · intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx.tower_top : IsIntegral (OpenOrder c) x)
    · rintro ⟨y,rfl⟩
      exact (IsIntegral.of_finite (ReciprocalOpen c) y).map
        (IsScalarTower.toAlgHom (ReciprocalOpen c) (OpenOrder c) (L c))

/-- Canonical integral-closure comparison preserves the actual embedding. -/
@[expose] def normalizationEquiv : OpenOrder c≃ₐ[ReciprocalOpen c]
    integralClosure (ReciprocalOpen c) (L c) := by
  let :=actual_integralClosure c
  exact IsIntegralClosure.equiv (ReciprocalOpen c) (OpenOrder c) (L c)
    (integralClosure (ReciprocalOpen c) (L c))

theorem normalizationEquiv_embedding (x:OpenOrder c) :
    (normalizationEquiv c x : L c)=InfinityOpenFractionField318.openEmbedding c x := by
  let :=actual_integralClosure c
  exact IsIntegralClosure.algebraMap_equiv (ReciprocalOpen c) (OpenOrder c) (L c)
    (integralClosure (ReciprocalOpen c) (L c)) x

open CategoryTheory AlgebraicGeometry
@[expose] def neighborhood : Scheme := Spec (CommRingCat.of (OpenOrder c))
@[expose] def base : Scheme := Spec (CommRingCat.of (ReciprocalOpen c))
@[expose] def structureMap : neighborhood c⟶base c :=
  Spec.map (CommRingCat.ofHom (chartMap c))

theorem structure_finite : IsFinite (structureMap c) :=
  (IsFinite.SpecMap_iff _).mpr (chartMap_finite c)

theorem structure_proper : IsProper (structureMap c) := by
  let :=structure_finite c
  infer_instance

/-- Smoothness is over Q via the actual etale u-coordinate presentation,
not over the ramified reciprocal s-line. -/
theorem neighborhood_smooth : Smooth
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (OpenOrder c)))) := by
  let : Algebra.Smooth ℚ R := ⟨inferInstance,inferInstance⟩
  let : Algebra.Etale (OpenBase c) (OpenOrder c):=(finite_free_etale_rank_eight c).2.2.1
  let : Algebra.Smooth ℚ (OpenBase c):=Algebra.Smooth.comp ℚ R (OpenBase c)
  let : Algebra.Smooth ℚ (OpenOrder c):=Algebra.Smooth.comp ℚ (OpenBase c) (OpenOrder c)
  exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
end ReciprocalInfinityNormalization318
