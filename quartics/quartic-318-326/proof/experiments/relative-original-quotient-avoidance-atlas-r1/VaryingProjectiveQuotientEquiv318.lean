module
public import VaryingProjectiveQuotientFreeCover318
public import VaryingLocalFreeConstantRank318
public section
noncomputable section
namespace VaryingProjectiveQuotientEquiv318
open VaryingLocalFreeQuotientEquiv318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- The usual finite-projective fixed-rank quotient functor, specified
entirely in terms of the literal original quotient algebra. -/
abbrev ProjectiveIdeal := {I : Ideal (S ⊗[R] A) //
  Module.Finite S ((S ⊗[R] A) ⧸ I) ∧ Module.Projective S ((S ⊗[R] A) ⧸ I) ∧
    ∀ x : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R] A) ⧸ I) x=Fintype.card ι}
@[expose] def toLocal (I : ProjectiveIdeal R A ι S) : LocalIdeal R A ι S := by
  letI := I.property.1
  letI := I.property.2.1
  exact ⟨I.val,⟨VaryingProjectiveQuotientFreeCover318.data R A ι S I.val I.property.2.2⟩⟩
@[expose] def fromLocal (I : LocalIdeal R A ι S) : ProjectiveIdeal R A ι S :=
  ⟨I.val,VaryingLocalFreeConstantRank318.finite_projective_rank R A ι S I⟩
@[expose] def localEquiv : ProjectiveIdeal R A ι S ≃ LocalIdeal R A ι S where
  toFun := toLocal R A ι S
  invFun := fromLocal R A ι S
  left_inv I := Subtype.ext rfl
  right_inv I := Subtype.ext rfl
/-- Genuine classification of all finite-projective original affine
quotients of the intended constant rank by ALL parameter-scheme points. -/
@[expose] def equivalence : ProjectiveIdeal R A ι S ≃ VaryingParameterPoint318.Point R A ι S :=
  (localEquiv R A ι S).trans (VaryingLocalFreeQuotientEquiv318.equivalence R A ι S)
lemma recovered_ideal (I : ProjectiveIdeal R A ι S) :
    VaryingParameterPointIdeal318.ideal R A ι S (equivalence R A ι S I)=I.val :=
  congrArg Subtype.val (recover_classify R A ι S (toLocal R A ι S I))
end VaryingProjectiveQuotientEquiv318
