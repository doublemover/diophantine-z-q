module
public import ContactBoundedCartierEquiv318
public section
noncomputable section
namespace ContactBoundedCartierKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedCartierEquiv318.Data c N b)
local notation "f" => ContactBoundedCartierEquiv318.forward c N b D
local notation "q" => D.val.ideal.subschemeι
local notation "r" => ContactBoundedPointFamily318.into c N b f.val
abbrev inputLine := ActualCartierIdealLine318.line q D.property
abbrev fiberLine := ActualCartierIdealLine318.line r f.property
/-- Actual O(-D) before and after bounded classification, with the
source sheaf inclusions identified, not merely their abstract classes. -/
@[expose] def comparison : (inputLine c N b D).object ≅ (fiberLine c N b D).object :=
  RegularClosedKernelTransport318.kernelIso q r
    (ContactBoundedInputRecovery318.comparison c N b D.val)
    (ContactBoundedInputRecovery318.comparison_source c N b D.val) D.property f.property
@[reassoc] lemma comparison_inclusion : (comparison c N b D).hom ≫ ActualClosedIdealModule318.inclusion r=
    ActualClosedIdealModule318.inclusion q := RegularClosedKernelTransport318.inclusion _ _ _ _ _ _
lemma divisor_class : classOf (FramedLineInverse318.inverse (inputLine c N b D))=
    classOf (FramedLineInverse318.inverse (fiberLine c N b D)) :=
  RegularClosedKernelTransport318.dual_class _ _ _ _ _ _
end ContactBoundedCartierKernel318
