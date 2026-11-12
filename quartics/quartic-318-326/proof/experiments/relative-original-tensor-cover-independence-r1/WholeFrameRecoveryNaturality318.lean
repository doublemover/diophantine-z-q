module
public import WholeFrameCoefficientNaturality318
public section
noncomputable section
namespace WholeFrameRecoveryNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B Y T T' : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
  (E : AffineRelativeFrameClassifier318.Data p L q)
  (b : T ⟶ B) (b' : T' ⟶ B) (h : T' ⟶ T) (hh : h ≫ b=b')
/-- Effective full-frame recovery is natural for arbitrary whole schemes,
with exactly the original coefficient morphism and native line associator. -/
lemma recovery (z : T ⟶ Y) (hz : z ≫ q=b) :
    WholeFrameCoefficientNaturality318.pullFrame p L b b' h hh
      (WholeParameterFrameRecovery318.recover p L q E b z hz)=
    WholeParameterFrameRecovery318.recover p L q E b' (h ≫ z)
      (by rw [Category.assoc,hz,hh]) := by
  apply (WholeFrameClassifierInverse318.equivalence p L q E b').symm.injective
  apply Subtype.ext
  change WholeFrameClassifyingRule318.classify p L q E b'
    (WholeFrameCoefficientNaturality318.pullFrame p L b b' h hh
      (WholeParameterFrameRecovery318.recover p L q E b z hz))=
    WholeFrameClassifyingRule318.classify p L q E b'
      (WholeParameterFrameRecovery318.recover p L q E b' (h ≫ z)
        (by rw [Category.assoc,hz,hh]))
  rw [WholeFrameCoefficientNaturality318.classify,
    WholeFrameClassifierInverse318.classify_recover,WholeFrameClassifierInverse318.classify_recover]
/-- The universal frame lives on the ACTUAL original family above the
same parameter scheme, and is recovered from its identity morphism. -/
@[expose] def universal : Frames (originalLine p L q) :=
  WholeParameterFrameRecovery318.recover p L q E q (𝟙 Y) (Category.id_comp q)
lemma universal_classify : WholeFrameClassifyingRule318.classify p L q E q
    (universal p L q E)=𝟙 Y :=
  WholeFrameClassifierInverse318.classify_recover p L q E q (𝟙 Y) (Category.id_comp q)
/-- Every classified frame is the actual native pullback of the universal
original frame, not just a matching isomorphism class or affine restriction. -/
lemma universal_pullback (z : T ⟶ Y) (hz : z ≫ q=b) :
    WholeFrameCoefficientNaturality318.pullFrame p L q b z hz (universal p L q E)=
      WholeParameterFrameRecovery318.recover p L q E b z hz := by
  simpa only [universal,Category.comp_id] using
    recovery p L q E q b z hz (𝟙 Y) (Category.id_comp q)
end WholeFrameRecoveryNaturality318
