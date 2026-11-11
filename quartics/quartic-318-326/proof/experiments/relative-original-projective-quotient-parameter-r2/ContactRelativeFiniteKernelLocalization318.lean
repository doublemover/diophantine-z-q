module
public import ContactRelativeFiniteLaurentPushout318
public import ContactRelativeGeneratorPresentations318
public import OriginalFreePresentationBaseChange318
public section
noncomputable section
namespace ContactRelativeFiniteKernelLocalization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) {ι : Type} (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

/-- The SAME original finite chart relations, mapped into the SAME
Laurent evaluation kernel of the given global generating family. -/
@[expose] def restriction :
    LinearMap.ker (ContactRelativeGeneratorPresentations318.finiteEvaluation R c L n g) →
      LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapFiniteEvaluation R c L n g) :=
  OriginalFreePresentationBaseChange318.kernelUnit (Polynomial R) (LaurentPolynomial R)
    (finiteSections R c L) (originalSections R c L)
    (ContactRelativeFiniteLaurentPushout318.sections R c L) (finiteRestriction R c L)
    (ContactRelativeFiniteLaurentPushout318.sections_unit R c L)
    (fun i => finiteGlobal R c L (n : ℤ) (g i))

/-- Actual finite polynomial kernel relations Laurent-span the original
whole overlap kernel. The section-localization and unit square are both
constructed, not caller-supplied premises. -/
theorem span (hg : Function.Surjective
    (ContactRelativeGeneratorPresentations318.finiteEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) (Set.range (restriction R c L n g)) = ⊤ :=
  OriginalFreePresentationBaseChange318.kernel_span (Polynomial R) (LaurentPolynomial R)
    (finiteSections R c L) (originalSections R c L)
    (ContactRelativeFiniteLaurentPushout318.sections R c L) (finiteRestriction R c L)
    (ContactRelativeFiniteLaurentPushout318.sections_unit R c L)
    (fun i => finiteGlobal R c L (n : ℤ) (g i)) hg
end ContactRelativeFiniteKernelLocalization318
