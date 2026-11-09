module
public import ContactIntegralRootGenericFiber318
public section
noncomputable section
namespace ContactIntegralPointScheme318
open ContactFieldRamification318 ContactIntegerEtaleCover318 ContactIntegerFractionField318
  ContactIntegerGenericFiber318 ContactIntegralRootPoint318 ContactIntegralRootGenericFiber318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

/-- The actual scheme-theoretic generic fiber of the integral four-root
model is the entire original specialized tensor fiber. -/
@[expose] def modelGenericIso (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    pullback (rationalToBase u v) (modelStructure u v) ≅
      Spec (CommRingCat.of (FourRootOrder318.Order (rationalParameters u v))) :=
  pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v) ≪≫
    Scheme.Spec.mapIso (genericOrderIso u v hn).toRingEquiv.toCommRingCatIso.symm.op

/-- The integral point after the actual rational base change. -/
@[expose] def genericPointMap (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    Spec (CommRingCat.of (L u v)) ⟶ pullback (rationalToBase u v) (modelStructure u v) :=
  Spec.map (CommRingCat.ofHom (genericPoint u v hn).toRingHom) ≫
    (pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v)).inv

@[reassoc] theorem genericPointMap_fst (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    genericPointMap u v hn ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (L u v))) := by
  change (Spec.map (CommRingCat.ofHom (ContactIntegralRootGenericFiber318.genericPoint u v hn).toRingHom) ≫
    (pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v)).inv) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing u v) ℚ)))
        (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing u v) (IntegralOrder u v)))) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  congr 1
  ext q
  exact (genericPoint u v hn).commutes q

/-- Its second projection is the original integer-cover point composed
with the unchanged original generic inclusion. -/
@[reassoc] theorem genericPointMap_snd (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    genericPointMap u v hn ≫ pullback.snd _ _ =
      genericToCover u v ≫ pointMap u v hn := by
  change (Spec.map (CommRingCat.ofHom (ContactIntegralRootGenericFiber318.genericPoint u v hn).toRingHom) ≫
    (pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v)).inv) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing u v) ℚ)))
        (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing u v) (IntegralOrder u v)))) = _
  rw [Category.assoc, pullbackSpecIso_inv_snd,
    genericToCover, pointMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change ContactIntegralRootGenericFiber318.genericPoint u v hn (1 ⊗ₜ[BaseRing u v] z) =
    integerToField u v (integralPoint u v hn z)
  simp [ContactIntegralRootGenericFiber318.genericPoint, integralPointToField]

/-- The resulting generic point is literally the original maximal-ideal
quotient point under the actual scheme generic-fiber identification. -/
theorem genericPointMap_original (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    genericPointMap u v hn ≫ (modelGenericIso u v hn).hom =
      Spec.map (CommRingCat.ofHom
        (RationalFourRootFiber318.point (rationalParameters u v)).toRingHom) := by
  change (Spec.map (CommRingCat.ofHom (genericPoint u v hn).toRingHom) ≫
    (pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v)).inv) ≫
      ((pullbackSpecIso (BaseRing u v) ℚ (IntegralOrder u v)).hom ≫
        Spec.map (CommRingCat.ofHom (genericOrderIso u v hn).symm.toRingHom)) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change ContactIntegralRootGenericFiber318.genericPoint u v hn ((genericOrderIso u v hn).symm z) = _
  rw [genericPoint_original]
  simp

/-- The original specialization map into the same complete contact source.
It is defined only on the rational generic fiber, not on the integral model. -/
@[expose] def originalSourceMap (u v : ℤ) :
    Spec (CommRingCat.of (FourRootOrder318.Order (rationalParameters u v))) ⟶
      ContactProjectiveModel318.model SourceTwistArithmetic318.units := by
  letI : Algebra (Polynomial ℚ) ℚ :=
    (Polynomial.aeval (32 * ((u : ℚ)/(v : ℚ)))).toRingHom.toAlgebra
  exact Spec.map (CommRingCat.ofHom
    (FourRootSignBaseChange318.coefficientMap
      (ContactKummerOrder318.coefficient SourceTwistArithmetic318.units) ℚ).toRingHom) ≫
        SourceGlobalAffine318.chartEmbedding SourceTwistArithmetic318.units

/-- The integral point's generic specialization recovers the exact original
point of the complete contact source, not just a related root tuple. -/
theorem original_source_point (u v : ℤ)
    (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    genericPointMap u v hn ≫ (modelGenericIso u v hn).hom ≫ originalSourceMap u v =
      RationalContactPoint318.point SourceTwistArithmetic318.units
        (32 * ((u : ℚ)/(v : ℚ))) := by
  rw [← Category.assoc, genericPointMap_original]
  unfold originalSourceMap RationalContactPoint318.point
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end ContactIntegralPointScheme318
