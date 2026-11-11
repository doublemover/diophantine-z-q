module
public import VaryingLocalFreeQuotientEquiv318
public section
noncomputable section
namespace VaryingLocalFreeQuotientNaturality318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open VaryingLocalFreeQuotientEquiv318
universe u
variable (R A ι S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  (f : S →ₐ[R] T)
/-- Literal ideal extension preserves the independent geometric
locally-free condition, for arbitrary coefficient maps. The now-proved
representation equivalence supplies an actual cover of the extension. -/
@[expose] def mapIdeal (I : LocalIdeal R A ι S) : LocalIdeal R A ι T :=
  ⟨Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom I.val,by
    let x := VaryingParameterPoint318.map R A ι S T f (classify R A ι S I)
    have h : VaryingParameterPointIdeal318.ideal R A ι T x=
        Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom I.val := by
      rw [VaryingPointIdealNaturality318.ideal_map]
      exact congrArg (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
        (congrArg Subtype.val (recover_classify R A ι S I))
    rw [← h]
    exact ⟨VaryingLocalFreeIdealCover318.ofPoint R A ι T x⟩⟩
lemma classify_natural (I : LocalIdeal R A ι S) :
    classify R A ι T (mapIdeal R A ι S T f I)=
      VaryingParameterPoint318.map R A ι S T f (classify R A ι S I) := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι T
  change (recover R A ι T (classify R A ι T (mapIdeal R A ι S T f I))).val=_
  rw [recover_classify,VaryingPointIdealNaturality318.ideal_map]
  exact (congrArg (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
    (congrArg Subtype.val (recover_classify R A ι S I))).symm
lemma recover_natural (x : VaryingParameterPoint318.Point R A ι S) :
    recover R A ι T (VaryingParameterPoint318.map R A ι S T f x)=
      mapIdeal R A ι S T f (recover R A ι S x) := by
  apply Subtype.ext
  exact VaryingPointIdealNaturality318.ideal_map R A ι S T f x
end VaryingLocalFreeQuotientNaturality318
