module
public import ContactIntegralRootPoint318
public section
noncomputable section
namespace ContactIntegralRootGenericFiber318
open NumberField ContactFieldRamification318 ContactIntegerEtaleCover318
  ContactIntegerFractionField318 ContactIntegerGenericLocalization318
  ContactIntegerRadicands318 ContactIntegralRootPoint318 FourRootOrder318 FourRootOrderSigns318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped NumberField TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

instance (u v : ℤ) : Algebra (BaseRing u v) (L u v) :=
  ((integerToField u v).comp (baseMap u v)).toAlgebra
instance coverFieldTower (u v : ℤ) :
    @IsScalarTower (BaseRing u v) (IntegerRing u v) (L u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl
instance rationalFieldTower (u v : ℤ) :
    @IsScalarTower (BaseRing u v) ℚ (L u v)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  exact field_square u v

lemma rational_parameter (u v : ℤ) (i : Fin 4) :
    algebraMap (BaseRing u v) ℚ (integralParameters u v i) = (radicand u v i : ℚ) := by
  change algebraMap (BaseRing u v) ℚ
    (algebraMap ℤ (BaseRing u v) (radicand u v i)) = _
  rw [← IsScalarTower.algebraMap_apply]
  rfl

@[expose] def scaleUnit (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) : ℚˣ :=
  Units.mk0 (v : ℚ) (by exact_mod_cast v_ne_zero u v hn)

lemma scale_parameters (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    algebraMap (BaseRing u v) ℚ (integralParameters u v i) =
      (scaleUnit u v hn : ℚ)^2 * rationalParameters u v i := by
  rw [rational_parameter]
  exact (scaled_parameter u v hn i).symm

/-- The entire generic fiber algebra of the literal integral model is the
original specialized contact tensor algebra, with the explicit scale v. -/
@[expose] def genericOrderIso (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    ℚ ⊗[BaseRing u v] IntegralOrder u v ≃ₐ[ℚ] Order (rationalParameters u v) :=
  (FourRootOrder318.baseChange (integralParameters u v) ℚ).trans
    (FourRootScaleEquiv318.equiv (rationalParameters u v)
      (fun i => algebraMap (BaseRing u v) ℚ (integralParameters u v i))
      (scaleUnit u v hn) (scale_parameters u v hn))

lemma genericOrderIso_generator (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0)
    (i : Fin 4) :
    genericOrderIso u v hn (1 ⊗ₜ[BaseRing u v] generator (integralParameters u v) i) =
      algebraMap ℚ (Order (rationalParameters u v)) (v : ℚ) *
        generator (rationalParameters u v) i := by
  change FourRootScaleEquiv318.equiv _ _ _ (scale_parameters u v hn)
    (FourRootSignBaseChange318.coefficientMap (integralParameters u v) ℚ
      (generator (integralParameters u v) i)) = _
  rw [FourRootSignBaseChange318.coefficientMap_generator, FourRootScaleEquiv318.equiv_generator]
  rfl

/-- Extension of the actual integral point by the original embedding S→L. -/
@[expose] def integralPointToField (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    IntegralOrder u v →ₐ[BaseRing u v] L u v :=
  { toRingHom := (integerToField u v).comp (integralPoint u v hn).toRingHom
    commutes' := by
      intro r
      change integerToField u v (integralPoint u v hn (algebraMap (BaseRing u v) (IntegralOrder u v) r)) = _
      rw [AlgHom.commutes]
      rfl }

/-- The actual base-changed integral point. -/
@[expose] def genericPoint (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    ℚ ⊗[BaseRing u v] IntegralOrder u v →ₐ[ℚ] L u v :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ (L u v)) (integralPointToField u v hn)
    (fun _ _ => Commute.all _ _)

/-- The full generic point equals the unchanged original maximal-ideal
quotient point after the explicit generic-fiber isomorphism. -/
theorem genericPoint_original (u v : ℤ) (hn : ∀ j, ContactRadical318.forms u v j ≠ 0) :
    genericPoint u v hn =
      (RationalFourRootFiber318.point (rationalParameters u v)).comp
        (genericOrderIso u v hn).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  apply FourRootSignBaseChange318.hom_ext
  intro i
  change genericPoint u v hn (1 ⊗ₜ[BaseRing u v] generator (integralParameters u v) i) =
    RationalFourRootFiber318.point _ (genericOrderIso u v hn
      (1 ⊗ₜ[BaseRing u v] generator (integralParameters u v) i))
  rw [genericOrderIso_generator, map_mul, AlgHom.commutes]
  simpa [genericPoint, integralPointToField, RationalFourRootFiber318.root] using
    integralPoint_original_generator u v hn i

end ContactIntegralRootGenericFiber318
