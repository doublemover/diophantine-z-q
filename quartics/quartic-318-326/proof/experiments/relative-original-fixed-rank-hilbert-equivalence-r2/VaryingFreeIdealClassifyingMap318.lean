module
public import VaryingCyclicFrameIndependence318
public section
noncomputable section
namespace VaryingFreeIdealClassifyingMap318
open AlgebraicGeometry CategoryTheory
open VaryingSourceFreeQuotientClassifier318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
abbrev IdealData := FreeQuotientFramedClassifier318.FreeIdeal S (S ⊗[R] A) ι
@[expose] def representative (I : IdealData R A ι S) : Cyclic R A ι S :=
  Classical.choose (source_ideal_surjective R A ι S I)
lemma representative_ideal (I : IdealData R A ι S) :
    FreeQuotientFramedClassifier318.toIdeal S (S ⊗[R] A) ι
      (toFramed R A ι S (representative R A ι S I))=I :=
  Classical.choose_spec (source_ideal_surjective R A ι S I)

/-- The actual global parameter point of a free full-ideal quotient.
The auxiliary chosen frame is proved irrelevant by classify_representative. -/
@[expose] def classify (I : IdealData R A ι S) : Spec (CommRingCat.of S) ⟶
    VaryingWordChartGluing318.scheme R A ι :=
  VaryingCyclicGlobalClassifyingMap318.classify R A ι S (representative R A ι S I)
lemma classify_representative (a : Cyclic R A ι S) :
    classify R A ι S (FreeQuotientFramedClassifier318.toIdeal S (S ⊗[R] A) ι (toFramed R A ι S a))=
      VaryingCyclicGlobalClassifyingMap318.classify R A ι S a :=
  VaryingCyclicFrameIndependence318.classify_eq R A ι S _ a
    (congrArg Subtype.val (representative_ideal R A ι S _))
@[reassoc] lemma over_base (I : IdealData R A ι S) :
    classify R A ι S I ≫ VaryingWordParameterStructure318.structureMap R A ι=
      VaryingSourceCoefficientPullback318.base R S :=
  VaryingCyclicGlobalClassifyingMap318.over_base R A ι S (representative R A ι S I)

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def mapIdeal (I : IdealData R A ι S) : IdealData R A ι T :=
  FreeQuotientFramedClassifier318.toIdeal T (T ⊗[R] A) ι
    (toFramed R A ι T (VaryingCyclicCoefficientSections318.mapCyclic
      R A ι S (representative R A ι S I) T f))
lemma mapIdeal_val (I : IdealData R A ι S) : (mapIdeal R A ι S T f I).val=
    Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom I.val := by
  have h := VaryingCyclicIdealBaseChange318.ideal_map R A ι S (representative R A ι S I) T f
  have hi := congrArg Subtype.val (representative_ideal R A ι S I)
  exact h.symm.trans (congrArg (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom) hi)

/-- A natural, basis-independent map from original globally free quotient
ideals to actual R-points of the glued scheme. Surjectivity onto all points
is deliberately NOT asserted: those can have only locally free quotients. -/
lemma natural (I : IdealData R A ι S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ classify R A ι S I=
      classify R A ι T (mapIdeal R A ι S T f I) :=
  (VaryingCyclicGlobalNaturality318.natural R A ι S (representative R A ι S I) T f).trans
    (classify_representative R A ι T
      (VaryingCyclicCoefficientSections318.mapCyclic R A ι S (representative R A ι S I) T f)).symm
end VaryingFreeIdealClassifyingMap318
