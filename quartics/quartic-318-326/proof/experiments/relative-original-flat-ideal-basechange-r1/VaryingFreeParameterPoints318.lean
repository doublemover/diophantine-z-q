module
public import VaryingClassifiedIdealRecovery318
public section
noncomputable section
namespace VaryingFreeParameterPoints318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- Intrinsic global freeness of the actual pulled-back quotient family.
This does not assert that every point is free and is not defined as the
range of the classifying map. The ideal exists independently for all points. -/
abbrev FreePoint := {x : VaryingParameterPoint318.Point R A ι S //
  Nonempty (Module.Basis ι S ((S ⊗[R] A) ⧸ VaryingParameterPointIdeal318.ideal R A ι S x))}
@[expose] def recover (x : FreePoint R A ι S) : VaryingFreeIdealClassifyingMap318.IdealData R A ι S :=
  ⟨VaryingParameterPointIdeal318.ideal R A ι S x.val,x.property⟩
@[expose] def classify (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) : FreePoint R A ι S :=
  ⟨VaryingParameterPoint318.ofIdeal R A ι S I,by
    rw [VaryingClassifiedIdealRecovery318.ideal_ofIdeal]
    exact I.property⟩
/-- A proved left inverse on the intrinsic free locus. The right inverse
is a separate obligation: this declaration is deliberately not an Equiv. -/
lemma recover_classify (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) :
    recover R A ι S (classify R A ι S I)=I := by
  apply Subtype.ext
  exact VaryingClassifiedIdealRecovery318.ideal_ofIdeal R A ι S I
lemma classify_injective : Function.Injective (classify R A ι S) :=
  Function.LeftInverse.injective (recover_classify R A ι S)
end VaryingFreeParameterPoints318
