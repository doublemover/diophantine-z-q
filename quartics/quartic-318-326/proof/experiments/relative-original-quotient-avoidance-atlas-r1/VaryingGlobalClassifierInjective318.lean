module
public import VaryingCyclicGlobalFamilyRecovery318
public import VaryingFreeIdealClassifyingMap318
public import AffineQuotientFactorRigidity318
public section
noncomputable section
namespace VaryingGlobalClassifierInjective318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a b : Cyclic R A ι S)
local notation "Qa" => VaryingCyclicFamilyBaseChange318.family R A ι S a
local notation "Qb" => VaryingCyclicFamilyBaseChange318.family R A ι S b
local notation "pa" => VaryingCyclicFamilyBaseChange318.projection R A ι S a
local notation "pb" => VaryingCyclicFamilyBaseChange318.projection R A ι S b
local notation "qa" => VaryingCyclicFamilyBaseChange318.into R A ι S a
local notation "qb" => VaryingCyclicFamilyBaseChange318.into R A ι S b
local notation "ma" => VaryingCyclicGlobalFamilyLift318.map R A ι S a
local notation "mb" => VaryingCyclicGlobalFamilyLift318.map R A ι S b
local notation "ca" => VaryingCyclicGlobalClassifyingMap318.classify R A ι S a
local notation "cb" => VaryingCyclicGlobalClassifyingMap318.classify R A ι S b
variable (h : ca=cb)
include h
lemma ideal_reverse_le :
    ideal (toFramed R A ι S b).action (toFramed R A ι S b).marked ≤
      ideal (toFramed R A ι S a).action (toFramed R A ι S a).marked := by
  have hw : ma ≫ VaryingWordGlobalFamilyProjection318.projection R A ι=pa ≫ cb :=
    (VaryingCyclicGlobalFamilyLift318.map_projection R A ι S a).trans (congrArg (fun k => pa ≫ k) h)
  let hb := VaryingCyclicGlobalFamilyRecovery318.cartesian R A ι S b
  let f : Qa ⟶ Qb := hb.lift ma pa hw
  have hf : f ≫ mb=ma := hb.lift_fst ma pa hw
  have hp : f ≫ pb=pa := hb.lift_snd ma pa hw
  have hsource : f ≫ qb=qa := by
    apply (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).hom_ext
    · simpa only [Category.assoc,VaryingCyclicFamilyBaseChange318.into_projection] using hp
    · rw [Category.assoc,← VaryingCyclicGlobalFamilyLift318.map_original R A ι S b,
        ← Category.assoc,hf,VaryingCyclicGlobalFamilyLift318.map_original R A ι S a]
  exact AffineQuotientFactorRigidity318.ideal_le (S ⊗[R] A) _ _ f hsource
/-- Equality of actual global classifying maps determines the WHOLE
original quotient ideal. Universal-family recovery supplies the proof. -/
lemma ideal_eq :
    ideal (toFramed R A ι S a).action (toFramed R A ι S a).marked=
      ideal (toFramed R A ι S b).action (toFramed R A ι S b).marked :=
  le_antisymm (ideal_reverse_le R A ι S b a h.symm) (ideal_reverse_le R A ι S a b h)

/-- The natural map on globally free quotient ideals is injective over
EVERY coefficient ring. Surjectivity onto all scheme points is not claimed. -/
omit h in
lemma classify_injective : Function.Injective (VaryingFreeIdealClassifyingMap318.classify R A ι S) := by
  intro I J hIJ
  apply Subtype.ext
  have he := ideal_eq R A ι S (VaryingFreeIdealClassifyingMap318.representative R A ι S I)
    (VaryingFreeIdealClassifyingMap318.representative R A ι S J) hIJ
  have hi := congrArg Subtype.val (VaryingFreeIdealClassifyingMap318.representative_ideal R A ι S I)
  have hj := congrArg Subtype.val (VaryingFreeIdealClassifyingMap318.representative_ideal R A ι S J)
  exact hi.symm.trans (he.trans hj)
end VaryingGlobalClassifierInjective318
