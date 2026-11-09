module
public import ContactIntegerGenericLocalization318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public section
noncomputable section
namespace ContactIntegerGenericFiber318
open NumberField ContactFieldRamification318 ContactIntegerEtaleCover318
  ContactIntegerFractionField318 ContactIntegerGenericLocalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped NumberField nonZeroDivisors
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

/-- The actual integer inclusion square is a pushout, with the original
rational algebra map to the original chosen contact field. -/
theorem ring_pushout (u v : ℤ) :
    IsPushout (CommRingCat.ofHom (baseMap u v))
      (CommRingCat.ofHom (baseToRational u v))
      (CommRingCat.ofHom (integerToField u v))
      (CommRingCat.ofHom (algebraMap ℚ (L u v))) := by
  let : IsLocalization ((Algebra.algebraMapSubmonoid (BaseRing u v) ℤ⁰).map
      (baseMap u v)) (L u v) := by
    rw [denominator_image]
    infer_instance
  exact CommRingCat.isPushout_of_isLocalization (baseMap u v)
    (algebraMap ℚ (L u v)) (field_square u v).symm
    (Algebra.algebraMapSubmonoid (BaseRing u v) ℤ⁰)

@[expose] def genericToCover (u v : ℤ) :
    Spec (CommRingCat.of (L u v)) ⟶ Spec (CommRingCat.of (IntegerRing u v)) :=
  Spec.map (CommRingCat.ofHom (integerToField u v))

@[expose] def rationalToBase (u v : ℤ) :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (BaseRing u v)) :=
  Spec.map (CommRingCat.ofHom (baseToRational u v))

/-- The unchanged field scheme is the actual generic fiber of the integral
cover, not only a scheme with an abstractly isomorphic function field. -/
theorem field_pullback (u v : ℤ) :
    IsPullback (genericToCover u v)
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (L u v))))
      (coverMap u v) (rationalToBase u v) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (ring_pushout u v)

@[expose] def genericFiberIso (u v : ℤ) :
    Spec (CommRingCat.of (L u v)) ≅ pullback (coverMap u v) (rationalToBase u v) :=
  (field_pullback u v).isoPullback

@[reassoc (attr := simp)] theorem genericFiberIso_fst (u v : ℤ) :
    (genericFiberIso u v).hom ≫ pullback.fst _ _ = genericToCover u v :=
  (field_pullback u v).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem genericFiberIso_snd (u v : ℤ) :
    (genericFiberIso u v).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (L u v))) :=
  (field_pullback u v).isoPullback_hom_snd

end ContactIntegerGenericFiber318
