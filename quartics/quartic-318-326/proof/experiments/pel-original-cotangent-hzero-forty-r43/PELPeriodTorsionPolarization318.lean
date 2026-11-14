module
public import PELLevelThreeAlternatingPair318
public import PELPeriodRiemannForm318
public section
noncomputable section
namespace PELPeriodTorsionPolarization318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318
open PELOriginalThirdPeriods318 PELOriginalThreeTorsion318 PELThreeTorsionOrderAction318
open PELLevelThreeAlternatingPair318
set_option maxHeartbeats 1200000
variable (τ : ℂ) (hτ : 0<τ.im)

/-- The finite alternating form lives on the full3-torsion of the original
compact period quotient, using its actual marked original-order thirds. -/
@[expose] def pair (x y : torsion τ) : F3 :=
  PELLevelThreeAlternatingPair318.pair ((torsionEquiv τ hτ).symm x)
    ((torsionEquiv τ hτ).symm y)

theorem alternating (x : torsion τ) : pair τ hτ x x=0 :=
  PELLevelThreeAlternatingPair318.alternating _

theorem add_left (x y z : torsion τ) : pair τ hτ (x+y) z=pair τ hτ x z+pair τ hτ y z := by
  simp only [pair,map_add,PELLevelThreeAlternatingPair318.add_left]

theorem add_right (x y z : torsion τ) : pair τ hτ x (y+z)=pair τ hτ x y+pair τ hτ x z := by
  simp only [pair,map_add,PELLevelThreeAlternatingPair318.add_right]

theorem nondegenerate (x : torsion τ) (hx : ∀ y,pair τ hτ x y=0) : x=0 := by
  apply (torsionEquiv τ hτ).symm.injective
  rw [map_zero]
  apply PELLevelThreeAlternatingPair318.nondegenerate
  intro b
  simpa only [pair,AddEquiv.symm_apply_apply] using hx (torsionEquiv τ hτ b)

theorem original_pair (a b : Coordinates) :
    pair τ hτ (torsionEquiv τ hτ (moduloThree.mk' (coordinatesEquiv a)))
      (torsionEquiv τ hτ (moduloThree.mk' (coordinatesEquiv b)))=
      (-(integralForm a b):ℤ) := by
  simp only [pair,AddEquiv.symm_apply_apply,PELLevelThreeAlternatingPair318.original_pair]

/-- The same positive Riemann form evaluates on the actual third-period
vectors with denominator9. No rescaling of μ or silent sign change occurs. -/
theorem original_riemann_thirds (a b : Coordinates) :
    PELPeriodRiemannForm318.riemann τ hτ (thirdVector τ (coordinatesEquiv a))
      (thirdVector τ (coordinatesEquiv b))=((-(integralForm a b):ℤ):ℝ)/9 := by
  change PELPeriodRiemannForm318.riemann τ hτ
    ((1/3:ℝ) • QuaternionicOrderPeriodQuotient318.periodHom
      PELQuaternionRealRepresentation318.representation τ (embed a))
    ((1/3:ℝ) • QuaternionicOrderPeriodQuotient318.periodHom
      PELQuaternionRealRepresentation318.representation τ (embed b))=_
  rw [PELPeriodRiemannForm318.smul_left,PELPeriodRiemannForm318.smul_right,
    PELPeriodRiemannForm318.original_integral]
  ring

/-- The finite form is exactly the mod3 numerator of3 times the original
Riemann form on order thirds: 3E(a/3,b/3)=−E_order(a,b)/3. This records the
normalization underlying the analytic level pairing, without naming an
unconstructed algebraic Weil pairing. -/
theorem original_normalization (a b : Coordinates) :
    3*PELPeriodRiemannForm318.riemann τ hτ (thirdVector τ (coordinatesEquiv a))
      (thirdVector τ (coordinatesEquiv b))=((-(integralForm a b):ℤ):ℝ)/3 ∧
    pair τ hτ (torsionEquiv τ hτ (moduloThree.mk' (coordinatesEquiv a)))
      (torsionEquiv τ hτ (moduloThree.mk' (coordinatesEquiv b)))=
      (-(integralForm a b):ℤ) := by
  constructor
  · rw [original_riemann_thirds]
    ring
  · exact original_pair τ hτ a b

theorem inverse_action (a : order) (x : torsion τ) :
    (torsionEquiv τ hτ).symm (torsionOrderEnd τ a x)=
      moduloThree.mk' a*(torsionEquiv τ hτ).symm x := by
  rw [← quotientAction_original τ hτ a]
  change (torsionEquiv τ hτ).symm (torsionEquiv τ hτ _)=_
  exact (torsionEquiv τ hτ).symm_apply_apply _

/-- The original geometric left action is adjoint to the same positive
quaternionic Rosati on the actual finite polarized torsion group. -/
theorem original_adjoint (a : order) (x y : torsion τ) :
    pair τ hτ (torsionOrderEnd τ a x) y=
      pair τ hτ x (torsionOrderEnd τ (orderRosati a) y) := by
  simp only [pair,inverse_action]
  exact PELLevelThreeAlternatingPair318.original_adjoint _ _ _
end PELPeriodTorsionPolarization318
