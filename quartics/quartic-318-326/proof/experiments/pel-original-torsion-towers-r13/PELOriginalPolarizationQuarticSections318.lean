module
public import PELOriginalQuarticGlobalRecovery318
public import PELOriginalPolarizationCube318
public section
noncomputable section
namespace PELOriginalPolarizationQuarticSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalSectionMultiplication318 PELOriginalMixedRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The proven quadratic power relation implies the fourth-power
relation in the quotient whose relation is ACTUAL sheaf isomorphism. -/
lemma class_power :
    classOf (LineSheafTensorPower318.line (line τ hτ) 4)=
      classOf (LineSheafTensorPower318.line (quadraticLine τ hτ) 2) := by
  have hc := PELOriginalPolarizationCube318.square_class τ hτ
  rw [LineSheafTensorPower318.classOf_power] at hc
  rw [LineSheafTensorPower318.classOf_power,LineSheafTensorPower318.classOf_power]
  change classOf (line τ hτ)^(2*2)=classOf (quadraticLine τ hτ)^2
  rw [pow_mul,hc]

/-- A full isomorphism of actual algebraic line sheaves. This choice is
not asserted to be a canonical normalized comparison. -/
@[expose] def quarticIso :
    (LineSheafTensorPower318.line (line τ hτ) 4).object ≅
      PELOriginalQuarticGlobalSections318.Power τ hτ :=
  Classical.choice ((classOf_eq_iff _ _).mp (class_power τ hτ))

/-- Every FULL original H0(4) section is realized as a genuine global
section of the actual degree-one algebraic line to power four. -/
@[expose] def sectionMap (s : homogeneous τ hτ 4) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶
      (LineSheafTensorPower318.line (line τ hτ) 4).object :=
  PELOriginalQuarticGlobalSections318.sectionMap τ hτ s ≫ (quarticIso τ hτ).inv

/-- Recovery is an equality of complete sheaf morphisms, not only of
complex-point values. -/
@[reassoc] theorem recover (s : homogeneous τ hτ 4) :
    sectionMap τ hτ s ≫ (quarticIso τ hτ).hom=
      PELOriginalQuarticGlobalSections318.sectionMap τ hτ s := by
  simp only [sectionMap,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Exact coefficients on every subopen after the actual full power
comparison. The same original regularization is retained. -/
theorem recover_subopen (s : homogeneous τ hτ 4) (a : NonemptyIndex τ hτ)
    (V : (candidate τ hτ).Opens) (hV : V ≤ opens τ hτ a) (c : Γ(candidate τ hτ,V)) :
    (sectionMap τ hτ s ≫ (quarticIso τ hτ).hom).app V c=
      OpenLineFrameCoordinates318.frame (PELOriginalQuarticGlobalSections318.Power τ hτ)
        (opens τ hτ a) (PELOriginalQuarticGlobalSections318.frame τ hτ a) V hV
        (c * (candidate τ hτ).presheaf.map (homOfLE hV).op
          (PELOriginalQuarticMixedCoefficients318.coefficient τ hτ a s)) := by
  rw [recover]
  exact PELOriginalQuarticGlobalSections318.sectionMap_subopen τ hτ s a V hV c
end PELOriginalPolarizationQuarticSections318
