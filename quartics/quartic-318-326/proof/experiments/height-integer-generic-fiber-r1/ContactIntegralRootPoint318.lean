module
public import ContactIntegerGenericFiber318
public import FourRootScaleEquiv318
public section
noncomputable section
namespace ContactIntegralRootPoint318
open NumberField ContactFieldRamification318 ContactIntegerEtaleLocus318
  ContactIntegerEtaleCover318 ContactIntegerFractionField318 ContactIntegerRadicands318
  FourRootOrder318 FourRootOrderSigns318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped NumberField
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

abbrev rationalParameters (u v : ℤ) :=
  RationalContactPoint318.parameters SourceTwistArithmetic318.units (32 * ((u : ℚ)/(v : ℚ)))

@[expose] def scaledRoot (u v : ℤ) (i : Fin 4) : L u v :=
  (v : L u v) * RationalFourRootFiber318.root (rationalParameters u v) i

lemma scaledRoot_square (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    scaledRoot u v i ^ 2 = (radicand u v i : L u v) := by
  change (algebraMap ℚ (L u v) (v : ℚ) *
    RationalFourRootFiber318.root (rationalParameters u v) i)^2 = _
  rw [mul_pow, RationalFourRootFiber318.root_square, ← map_pow, ← map_mul,
    scaled_parameter u v hn i]
  simp

/-- The actual scaled root lies in the original full ring of integers. -/
@[expose] def integerRoot (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0)
    (i : Fin 4) : 𝓞 (L u v) :=
  ⟨scaledRoot u v i, (show IsIntegral ℤ (scaledRoot u v i ^ 2) by
    rw [scaledRoot_square u v hn i]
    exact isIntegral_algebraMap).of_pow (by decide : 0 < 2)⟩

lemma integerRoot_square (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    integerRoot u v hn i ^ 2 = (radicand u v i : 𝓞 (L u v)) := by
  apply Subtype.ext
  exact scaledRoot_square u v hn i

abbrev integralParameters (u v : ℤ) : Fin 4 → BaseRing u v :=
  fun i => algebraMap ℤ (BaseRing u v) (radicand u v i)
abbrev IntegralOrder (u v : ℤ) := Order (integralParameters u v)

/-- A literal finite free degree-sixteen integral model of the specialized
four-root fiber. It is not asserted to be smooth at its even-contact primes. -/
theorem integralOrder_finite_free (u v : ℤ) :
    Module.Finite (BaseRing u v) (IntegralOrder u v) ∧
      Module.Free (BaseRing u v) (IntegralOrder u v) := finite_free _

theorem integralOrder_rank (u v : ℤ) :
    Module.finrank (BaseRing u v) (IntegralOrder u v) = 16 := by
  let : IsDomain (BaseRing u v) := Localization.Away.isDomain (by
    exact_mod_cast (Nat.ne_of_gt (excludedProduct_pos u v)))
  exact FourRootOrder318.rank_sixteen _

/-- The integral point of the literal specialized model, on the exact finite
etale S-integer cover already constructed. -/
@[expose] def integralPoint (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    IntegralOrder u v →ₐ[BaseRing u v] IntegerRing u v :=
  FourRootPointUniversal318.point (integralParameters u v)
    (fun i => algebraMap (𝓞 (L u v)) (IntegerRing u v) (integerRoot u v hn i)) (by
      intro i
      rw [← map_pow, integerRoot_square]
      change algebraMap (𝓞 (L u v)) (IntegerRing u v)
        (algebraMap ℤ (𝓞 (L u v)) (radicand u v i)) =
        algebraMap (BaseRing u v) (IntegerRing u v)
          (algebraMap ℤ (BaseRing u v) (radicand u v i))
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])

@[simp] theorem integralPoint_generator (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    integralPoint u v hn (generator (integralParameters u v) i) =
      algebraMap (𝓞 (L u v)) (IntegerRing u v) (integerRoot u v hn i) :=
  FourRootPointUniversal318.point_generator _ _ _ _

/-- Every integral generator maps to exactly v times its original contact
root under the unchanged generic-field embedding. -/
theorem integralPoint_original_generator (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    integerToField u v (integralPoint u v hn (generator (integralParameters u v) i)) =
      (v : L u v) * RationalFourRootFiber318.root (rationalParameters u v) i := by
  rw [integralPoint_generator, integerToField_original]
  rfl

@[expose] def model (u v : ℤ) : Scheme := Spec (CommRingCat.of (IntegralOrder u v))
@[expose] def modelStructure (u v : ℤ) : model u v ⟶ Spec (CommRingCat.of (BaseRing u v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseRing u v) (IntegralOrder u v)))
@[expose] def pointMap (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    Spec (CommRingCat.of (IntegerRing u v)) ⟶ model u v :=
  Spec.map (CommRingCat.ofHom (integralPoint u v hn).toRingHom)

/-- The extended point lies over the actual cover map, not a substituted
isomorphic base or an asserted rational section. -/
theorem pointMap_over_base (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    pointMap u v hn ≫ modelStructure u v = coverMap u v := by
  rw [pointMap, modelStructure, coverMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (integralPoint u v hn).commutes x

/-- Finiteness and flatness concern the literal integral model itself. They
are not inferred from its generic fiber or from the etale cover. -/
theorem model_finite_flat (u v : ℤ) :
    IsFinite (modelStructure u v) ∧ Flat (modelStructure u v) := by
  let : Module.Finite (BaseRing u v) (IntegralOrder u v) := (integralOrder_finite_free u v).1
  let : Module.Free (BaseRing u v) (IntegralOrder u v) := (integralOrder_finite_free u v).2
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  · apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_free (R := BaseRing u v) (M := IntegralOrder u v))

@[expose] def pointSection (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    Spec (CommRingCat.of (IntegerRing u v)) ⟶
      pullback (modelStructure u v) (coverMap u v) :=
  pullback.lift (pointMap u v hn) (𝟙 _)
    (by simpa using pointMap_over_base u v hn)

@[reassoc] theorem pointSection_fst (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    pointSection u v hn ≫ pullback.fst _ _ = pointMap u v hn :=
  pullback.lift_fst _ _ _

@[reassoc] theorem pointSection_snd (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    pointSection u v hn ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

end ContactIntegralRootPoint318
