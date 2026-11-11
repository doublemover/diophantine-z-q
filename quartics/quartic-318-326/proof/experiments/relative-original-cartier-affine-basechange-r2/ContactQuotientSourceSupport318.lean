module
public import ContactQuotientOverlapEquiv318
public section
noncomputable section
namespace ContactQuotientSourceSupport318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n)
@[expose] def source : family c a S n I ⟶ ContactProjectiveModel318.model c :=
  quotientInto c a S n I ≫ VaryingSourceCoefficientPullback318.original ℚ (ring c a) S ≫ original c a
@[reassoc] lemma projective_source : projectiveInto c a S n I ≫
    pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
      (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)=source c a S n I := by
  change (quotientInto c a S n I ≫ into c a S) ≫ _=_
  rw [Category.assoc,RelativeOriginalAffineChart318.over_original]
  rfl
/-- Support is the WHOLE original source support, independent of a
coefficient chart presentation or rational-point selection. -/
lemma supported_iff : Supported c a b S n I ↔ ∀ z : family c a S n I,
    source c a S n I z ∈ Set.range (original c b) := by
  constructor
  · intro h z
    have hz := h ⟨z,rfl⟩
    change projectiveInto c a S n I z∈(into c b S).opensRange at hz
    rw [RelativeOriginalAffineChart318.range] at hz
    change (projectiveInto c a S n I ≫ pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
      (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)) z∈(original c b).opensRange at hz
    rw [projective_source] at hz
    exact hz
  · intro h
    change Set.range (projectiveInto c a S n I) ⊆ (into c b S).opensRange
    rw [RelativeOriginalAffineChart318.range]
    rintro _ ⟨z,rfl⟩
    change (projectiveInto c a S n I ≫ pullback.fst (ContactIntrinsicDifferentials318.structureMap c)
      (RelativeOriginalAffineChart318.baseMap (CommRingCat.of ℚ) S)) z∈(original c b).opensRange
    rw [projective_source]
    exact h z
end ContactQuotientSourceSupport318
