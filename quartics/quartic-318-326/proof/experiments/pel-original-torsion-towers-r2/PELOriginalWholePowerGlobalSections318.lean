module
public import FramedLineCoefficientGluing318
public import PELOriginalWholePowerMixedTransition318
public section
noncomputable section
namespace PELOriginalWholePowerGlobalSections318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalSectionMultiplication318
open PELOriginalWholePowerMixedCoefficient318 PELOriginalWholePowerMixedTransition318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The actual iterated tensor power of the original algebraic cubic
hyperplane sheaf. -/
abbrev power := FramedLineTensorPower318.object (cubicSheaf τ hτ) m
@[expose] def frame (a : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ a).toScheme.ringCatSheaf ≅
      (power τ hτ m).restrict (opens τ hτ a).ι :=
  FramedLineTensorPower318.frames (cubicSheaf τ hτ) (opens τ hτ)
    (cubicFrame τ hτ) m a

/-- Every original holomorphic section of degree3m gives a genuine
GLOBAL section of the whole algebraic tensor-power sheaf. -/
@[expose] def global (s : homogeneous τ hτ (3*m)) : Γ(power τ hτ m,⊤) :=
  FramedLineCoefficientGluing318.global (power τ hτ m) (opens τ hτ) (frame τ hτ m)
    (fun a => originalCoefficient τ hτ m a s)
    (fun a b => original_transition τ hτ m a b s) (coversTop τ hτ)

@[expose] def sectionMap (s : homogeneous τ hτ (3*m)) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ power τ hτ m :=
  FramedLineCoefficientGluing318.sectionMap (power τ hτ m) (opens τ hτ) (frame τ hτ m)
    (fun a => originalCoefficient τ hτ m a s)
    (fun a b => original_transition τ hτ m a b s) (coversTop τ hτ)

/-- Exact local coefficients on each whole chart. -/
theorem global_restrict (s : homogeneous τ hτ (3*m)) (a : NonemptyIndex τ hτ) :
    (power τ hτ m).presheaf.map (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op
      (global τ hτ m s)=
    OpenLineFrameCoordinates318.frame (power τ hτ m) (opens τ hτ a)
      (frame τ hτ m a) (opens τ hτ a) le_rfl (originalCoefficient τ hτ m a s) :=
  FramedLineCoefficientGluing318.global_restrict _ _ _ _ _ _ a

/-- The construction is a full sheaf section, with exact action on
EVERY subopen and arbitrary ring section, including degree zero. -/
theorem sectionMap_subopen (s : homogeneous τ hτ (3*m)) (a : NonemptyIndex τ hτ)
    (V : (candidate τ hτ).Opens) (hV : V ≤ opens τ hτ a) (c : Γ(candidate τ hτ,V)) :
    (sectionMap τ hτ m s).app V c=
      OpenLineFrameCoordinates318.frame (power τ hτ m) (opens τ hτ a)
        (frame τ hτ m a) V hV
        (c * (candidate τ hτ).presheaf.map (homOfLE hV).op
          (originalCoefficient τ hτ m a s)) :=
  FramedLineCoefficientGluing318.sectionMap_subopen _ _ _ _ _ _ a V hV c

/-- No choices of primitive element or gluing survive: the full
regular coefficients uniquely determine this global section. -/
theorem unique (s : homogeneous τ hτ (3*m)) (t : Γ(power τ hτ m,⊤))
    (ht : ∀ a : NonemptyIndex τ hτ,
      (power τ hτ m).presheaf.map (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op t=
      OpenLineFrameCoordinates318.frame (power τ hτ m) (opens τ hτ a)
        (frame τ hτ m a) (opens τ hτ a) le_rfl (originalCoefficient τ hτ m a s)) :
    t=global τ hτ m s :=
  FramedLineCoefficientGluing318.global_unique _ _ _ _ _ _ t ht

lemma originalCoefficient_add (a : NonemptyIndex τ hτ) (s t : homogeneous τ hτ (3*m)) :
    originalCoefficient τ hτ m a (s+t)=
      originalCoefficient τ hτ m a s+originalCoefficient τ hτ m a t := by
  simp only [originalCoefficient,coefficient,map_add]
lemma originalCoefficient_zero (a : NonemptyIndex τ hτ) :
    originalCoefficient τ hτ m a (0 : homogeneous τ hτ (3*m))=0 := by
  simp only [originalCoefficient,coefficient,map_zero]

theorem global_add (s t : homogeneous τ hτ (3*m)) :
    global τ hτ m (s+t)=global τ hτ m s+global τ hτ m t := by
  symm
  apply unique
  intro a
  rw [map_add,global_restrict,global_restrict,originalCoefficient_add,map_add]
theorem global_zero : global τ hτ m (0 : homogeneous τ hτ (3*m))=0 := by
  symm
  apply unique
  intro a
  rw [map_zero,originalCoefficient_zero,map_zero]

/-- Actual additive algebraization of the FULL original section space,
not merely an assignment on a theta basis. -/
@[expose] def additive : homogeneous τ hτ (3*m) →+ Γ(power τ hτ m,⊤) where
  toFun := global τ hτ m
  map_zero' := global_zero τ hτ m
  map_add' := global_add τ hτ m
end PELOriginalWholePowerGlobalSections318
