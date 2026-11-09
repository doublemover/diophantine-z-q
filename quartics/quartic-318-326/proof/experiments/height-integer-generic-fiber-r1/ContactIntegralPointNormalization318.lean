module
public import ContactIntegralPointScheme318
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace ContactIntegralPointNormalization318
open ContactFieldRamification318 ContactIntegerEtaleLocus318 ContactIntegerEtaleCover318
  ContactIntegerFractionField318 ContactIntegralRootPoint318 ContactIntegralRootGenericFiber318
open AlgebraicGeometry CategoryTheory
open scoped NumberField nonZeroDivisors
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

instance integerRing_normal (u v : ℤ) : IsIntegrallyClosed (IntegerRing u v) := by
  apply isIntegrallyClosed_of_isLocalization (IntegerRing u v)
    (Submonoid.powers (algebraMap ℤ (𝓞 (L u v)) (excludedProduct u v : ℤ)))
  apply Submonoid.powers_le.mpr
  rw [mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 (L u v)))]
  exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v))

/-- The actual S-integer cover is the full integral closure of the actual
S-integer base inside the unchanged original contact field. -/
instance baseIntegralClosure (u v : ℤ) :
    IsIntegralClosure (IntegerRing u v) (BaseRing u v) (L u v) :=
  IsIntegralClosure.of_isIntegrallyClosed (IntegerRing u v) (BaseRing u v) (L u v)

variable (u v : ℤ) [hn : Fact (∀ j, ContactRadical318.forms u v j ≠ 0)]

local instance : Algebra (IntegralOrder u v) (IntegerRing u v) :=
  (integralPoint u v hn.out).toRingHom.toAlgebra
local instance : Algebra (IntegralOrder u v) (L u v) :=
  (integralPointToField u v hn.out).toRingHom.toAlgebra
local instance :
    @IsScalarTower (BaseRing u v) (IntegralOrder u v) (IntegerRing u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  ext r
  exact (integralPoint u v hn.out).commutes r |>.symm
local instance :
    @IsScalarTower (IntegralOrder u v) (IntegerRing u v) (L u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- Normalization of the literal specialized fiber in its actual selected
generic point produces the same S-integer ring, not a new field or cover. -/
theorem pointIntegralClosure :
    IsIntegralClosure (IntegerRing u v) (IntegralOrder u v) (L u v) := by
  let : Algebra.IsIntegral (IntegralOrder u v) (IntegerRing u v) :=
    Algebra.IsIntegral.tower_top (BaseRing u v)
  exact IsIntegralClosure.of_isIntegrallyClosed (IntegerRing u v) (IntegralOrder u v) (L u v)

/-- The full integral-closure algebra, with its actual selected generic map,
is explicitly identified with the preceding finite etale cover algebra. -/
@[expose] def normalizationEquiv : IntegerRing u v ≃ₐ[IntegralOrder u v]
    integralClosure (IntegralOrder u v) (L u v) := by
  let := pointIntegralClosure u v
  exact IsIntegralClosure.equiv (IntegralOrder u v) (IntegerRing u v) (L u v)
    (integralClosure (IntegralOrder u v) (L u v))

lemma normalizationEquiv_original (x : IntegerRing u v) :
    algebraMap (integralClosure (IntegralOrder u v) (L u v)) (L u v)
      (normalizationEquiv u v x) = integerToField u v x := by
  let := pointIntegralClosure u v
  simpa only [normalizationEquiv, RingHom.algebraMap_toAlgebra] using
    IsIntegralClosure.algebraMap_equiv (IntegralOrder u v) (IntegerRing u v)
      (L u v) (integralClosure (IntegralOrder u v) (L u v)) x

/-- Spec of the actual integral-closure ring in the selected original field. -/
@[expose] def closureModel : Scheme :=
  Spec (CommRingCat.of (integralClosure (IntegralOrder u v) (L u v)))
@[expose] def closureMap : closureModel u v ⟶ model u v :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (IntegralOrder u v) (integralClosure (IntegralOrder u v) (L u v))))

@[expose] def ringEquivSpecIso {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of B) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.symm.op

@[simp] theorem ringEquivSpecIso_hom {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) : (ringEquivSpecIso e).hom =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) := rfl

/-- The same accepted finite etale cover is the actual affine integral-
closure model, with no change of field or underlying rational embedding. -/
@[expose] def closureIso : Spec (CommRingCat.of (IntegerRing u v)) ≅ closureModel u v :=
  ringEquivSpecIso (A := IntegerRing u v)
    (B := integralClosure (IntegralOrder u v) (L u v))
    (normalizationEquiv u v).toRingEquiv

@[reassoc] theorem closureIso_over_model :
    (closureIso u v).hom ≫ closureMap u v = pointMap u v hn.out := by
  rw [closureIso, ringEquivSpecIso_hom, closureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (normalizationEquiv u v).symm.commutes z

@[reassoc] theorem closureIso_over_base :
    (closureIso u v).hom ≫ closureMap u v ≫ modelStructure u v = coverMap u v := by
  rw [← Category.assoc, closureIso_over_model, pointMap_over_base]

end ContactIntegralPointNormalization318
