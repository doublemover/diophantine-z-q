module
public import PELOriginalWholePowerGlobalRecovery318
public import PELOriginalPolarizationCube318
public section
noncomputable section
namespace PELOriginalPolarizationPowerGlobalSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalSectionMultiplication318 PELOriginalMixedRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The proven cubic power relation implies the full mth-power
relation in the quotient whose relation is ACTUAL sheaf isomorphism. -/
lemma class_power :
    classOf (LineSheafTensorPower318.line (line τ hτ) (3*m))=
      classOf (LineSheafTensorPower318.line (cubicLine τ hτ) m) := by
  have hc := PELOriginalPolarizationCube318.cube_class τ hτ
  rw [LineSheafTensorPower318.classOf_power] at hc
  rw [LineSheafTensorPower318.classOf_power,LineSheafTensorPower318.classOf_power,
    pow_mul,hc]

/-- A full isomorphism of actual algebraic line sheaves. This choice is
not asserted to be a canonical normalized comparison. -/
@[expose] def powerIso :
    (LineSheafTensorPower318.line (line τ hτ) (3*m)).object ≅
      PELOriginalWholePowerGlobalSections318.power τ hτ m :=
  Classical.choice ((classOf_eq_iff _ _).mp (class_power τ hτ m))

/-- Every FULL original H0(3m) section is realized as a genuine global
section of the actual degree-one algebraic line to power3m. -/
@[expose] def sectionMap (s : homogeneous τ hτ (3*m)) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶
      (LineSheafTensorPower318.line (line τ hτ) (3*m)).object :=
  PELOriginalWholePowerGlobalSections318.sectionMap τ hτ m s ≫ (powerIso τ hτ m).inv

/-- Recovery is an equality of complete sheaf morphisms, not only of
complex-point values. -/
@[reassoc] theorem recover (s : homogeneous τ hτ (3*m)) :
    sectionMap τ hτ m s ≫ (powerIso τ hτ m).hom=
      PELOriginalWholePowerGlobalSections318.sectionMap τ hτ m s := by
  simp only [sectionMap,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Exact coefficients on every subopen after the actual full power
comparison. The same original regularization is retained. -/
theorem recover_subopen (s : homogeneous τ hτ (3*m)) (a : NonemptyIndex τ hτ)
    (V : (candidate τ hτ).Opens) (hV : V ≤ opens τ hτ a) (c : Γ(candidate τ hτ,V)) :
    (sectionMap τ hτ m s ≫ (powerIso τ hτ m).hom).app V c=
      OpenLineFrameCoordinates318.frame (PELOriginalWholePowerGlobalSections318.power τ hτ m)
        (opens τ hτ a) (PELOriginalWholePowerGlobalSections318.frame τ hτ m a) V hV
        (c * (candidate τ hτ).presheaf.map (homOfLE hV).op
          (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ m a s)) := by
  rw [recover]
  exact PELOriginalWholePowerGlobalSections318.sectionMap_subopen τ hτ m s a V hV c
end PELOriginalPolarizationPowerGlobalSections318
