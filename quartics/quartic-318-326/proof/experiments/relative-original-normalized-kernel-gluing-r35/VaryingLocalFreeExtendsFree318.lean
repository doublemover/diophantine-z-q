module
public import VaryingLocalFreeFamilyRecovery318
public section
noncomputable section
namespace VaryingLocalFreeExtendsFree318
open AlgebraicGeometry CategoryTheory
open VaryingLocalFreeQuotientEquiv318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- On globally free quotients the new all-point classifier is EXACTLY
the old proven classifier. The extension does not replace the original
source, point, full ideal or universal family. -/
lemma classify_free (I : LocalIdeal R A ι S)
    (h : Nonempty (Module.Basis ι S ((S ⊗[R] A) ⧸ I.val))) :
    classify R A ι S I=VaryingParameterPoint318.ofIdeal R A ι S ⟨I.val,h⟩ := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι S
  rw [VaryingClassifiedIdealRecovery318.ideal_ofIdeal]
  exact congrArg Subtype.val (recover_classify R A ι S I)
end VaryingLocalFreeExtendsFree318
