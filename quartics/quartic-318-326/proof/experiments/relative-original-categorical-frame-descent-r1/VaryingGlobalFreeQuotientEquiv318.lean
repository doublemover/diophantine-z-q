module
public import VaryingFreePointGlobalInverse318
public section
noncomputable section
namespace VaryingGlobalFreeQuotientEquiv318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- The natural all-ring global classifier, with its CORRECT image:
actual points whose original universal quotient is globally free of the
specified rank. This does not identify arbitrary locally free points with
free ideals, nor claim Picard/Jacobian representability. -/
@[expose] def equivalence : VaryingFreeIdealClassifyingMap318.IdealData R A ι S ≃
    VaryingFreeParameterPoints318.FreePoint R A ι S where
  toFun := VaryingFreeParameterPoints318.classify R A ι S
  invFun := VaryingFreeParameterPoints318.recover R A ι S
  left_inv := VaryingFreeParameterPoints318.recover_classify R A ι S
  right_inv := VaryingFreePointGlobalInverse318.classify_recover R A ι S
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma natural (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) :
    VaryingPointIdealNaturality318.mapFree R A ι S T f (equivalence R A ι S I)=
      equivalence R A ι T (VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f I) :=
  VaryingPointIdealNaturality318.classify_natural R A ι S T f I
lemma inverse_natural (x : VaryingFreeParameterPoints318.FreePoint R A ι S) :
    (equivalence R A ι T).symm (VaryingPointIdealNaturality318.mapFree R A ι S T f x)=
      VaryingFreeIdealClassifyingMap318.mapIdeal R A ι S T f ((equivalence R A ι S).symm x) :=
  VaryingPointIdealNaturality318.recover_natural R A ι S T f x
lemma family_recovery (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S) :
    Nonempty (VaryingFreeIdealFamilyRecovery318.family R A ι S I ≅
      CategoryTheory.Limits.pullback (VaryingWordGlobalFamilyProjection318.projection R A ι)
        (equivalence R A ι S I).val.val) :=
  ⟨VaryingFreeIdealFamilyRecovery318.comparison R A ι S I⟩
end VaryingGlobalFreeQuotientEquiv318
