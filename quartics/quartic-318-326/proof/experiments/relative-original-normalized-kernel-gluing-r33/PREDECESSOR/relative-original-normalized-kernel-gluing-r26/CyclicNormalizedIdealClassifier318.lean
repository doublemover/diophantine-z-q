module
public import CyclicNormalizedFrameUniqueness318
public section
noncomputable section
namespace CyclicNormalizedIdealClassifier318
open CyclicQuotientEvaluation318 CyclicQuotientKernel318
open FreeQuotientFramedClassifier318 CyclicWordNormalization318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → A)
abbrev NormalizedFrames := {d : Framed R A ι // Normalized R A ι d w}
/-- The SAME selected source elements must be a basis in the literal
ideal quotient, not just some basis of the correct rank. -/
abbrev WordIdeal := {I : Ideal A // ∃ b : Module.Basis ι R (A ⧸ I),
  ∀ j, b j=Ideal.Quotient.mk I (w j)}

@[expose] def toWordIdeal (d : NormalizedFrames R A ι w) : WordIdeal R A ι w :=
  ⟨ideal d.val.action d.val.marked,⟨quotientBasis d.val.action d.val.marked
    (VaryingSourceWordQuotient318.standardBasis ι R) d.val.cyclic,by
      intro j
      apply (quotientEquiv d.val.action d.val.marked d.val.cyclic).injective
      rw [quotientBasis_image,quotientEquiv_mk]
      change (VaryingSourceWordQuotient318.standardBasis ι R) j=
        evaluation d.val.action d.val.marked (w j)
      rw [d.property j]
      exact congrFun (Module.Basis.coe_ofEquivFun (LinearEquiv.refl R (ι → R))) j⟩⟩

lemma fromBasis_normalized (I : Ideal A) (b : Module.Basis ι R (A ⧸ I))
    (hb : ∀ j, b j=Ideal.Quotient.mk I (w j)) :
    Normalized R A ι (fromBasis R A ι I b) w := by
  intro j
  change b.equivFun (Ideal.Quotient.mk I (w j) *
    b.equivFun.symm (b.equivFun (1 : A ⧸ I)))=Pi.single j 1
  rw [LinearEquiv.symm_apply_apply,mul_one,← hb j]
  ext i
  simp only [Module.Basis.equivFun_self,Pi.single_apply,eq_comm]

lemma toWordIdeal_bijective : Function.Bijective (toWordIdeal R A ι w) := by
  constructor
  · intro d e h
    apply Subtype.ext
    apply CyclicNormalizedFrameUniqueness318.eq_of_ideal R A ι d.val e.val w d.property e.property
    apply Subtype.ext
    exact congrArg Subtype.val h
  · rintro ⟨I,⟨b,hb⟩⟩
    refine ⟨⟨fromBasis R A ι I b,fromBasis_normalized R A ι w I b hb⟩,?_⟩
    apply Subtype.ext
    exact fromBasis_ideal R A ι I b

/-- Fixed-word normalized frames classify exactly the full ideals for
which those very word images form a basis, over every coefficient ring. -/
@[expose] def classifier : NormalizedFrames R A ι w ≃ WordIdeal R A ι w :=
  Equiv.ofBijective (toWordIdeal R A ι w) (toWordIdeal_bijective R A ι w)
end CyclicNormalizedIdealClassifier318
