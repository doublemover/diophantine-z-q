module
public import PELOriginalTranslationLineClass318
public section
noncomputable section
namespace PELOriginalTranslationDifferenceFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalPolarizationTransitions318
open PELOriginalProductChartCover318 PELOriginalCandidateComplexPoints318
open PELOriginalTranslationAutomorphisms318 PELOriginalTranslationLineClass318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev first : Product τ hτ ⟶ candidate τ hτ := pullback.fst _ _
abbrev second : Product τ hτ ⟶ candidate τ hτ := pullback.snd _ _

/-- A genuine line sheaf on the ENTIRE actual scheme product:
m^*L tensor (pr_1^*L)^{-1}. The second factor is the parameter. -/
@[expose] def family : Line (Product τ hτ) :=
  LineSheafTensor318.line
    (LineSheafPullback318.line (PELOriginalAdditionSchemeMorphism318.addition τ hτ)
      (PELOriginalAlgebraicPolarizationLine318.line τ hτ))
    (FramedLineInverse318.inverse (LineSheafPullback318.line (first τ hτ)
      (PELOriginalAlgebraicPolarizationLine318.line τ hτ)))

/-- The literal fiber inclusion x ↦ (x,q), through the actual pullback. -/
@[expose] def slice (q : Base τ) : candidate τ hτ ⟶ Product τ hτ :=
  pullback.lift (𝟙 _) (π τ hτ ≫ candidateComplexPoint τ hτ q)
    (by rw [Category.id_comp,Category.assoc,
      PELOriginalProperComplexCandidate318.candidate_point_over,Category.comp_id])
@[reassoc] lemma slice_first (q : Base τ) : slice τ hτ q ≫ first τ hτ=𝟙 _ :=
  pullback.lift_fst _ _ _
@[reassoc] lemma slice_second (q : Base τ) :
    slice τ hτ q ≫ second τ hτ=π τ hτ ≫ candidateComplexPoint τ hτ q :=
  pullback.lift_snd _ _ _
lemma slice_addition (q : Base τ) :
    slice τ hτ q ≫ PELOriginalAdditionSchemeMorphism318.addition τ hτ=
      translation τ hτ q := rfl

/-- Pullback of the WHOLE family to its literal q-fiber is the actual
translation-difference line. The isomorphism exists through full sheaf
pullback/tensor comparison, not merely equality on closed-point fibers. -/
@[expose] def fiberIso (q : Base τ) :
    (LineSheafPullback318.line (slice τ hτ q) (family τ hτ)).object ≅
      (differenceLine τ hτ q).object := by
  let L := PELOriginalAlgebraicPolarizationLine318.line τ hτ
  let A := LineSheafPullback318.line (PELOriginalAdditionSchemeMorphism318.addition τ hτ) L
  let B := LineSheafPullback318.line (first τ hτ) L
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  change LineClassPullbackGroup318.hom (slice τ hτ q)
    (classOf (LineSheafTensor318.line A (FramedLineInverse318.inverse B))) = _
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,
    map_mul,map_inv]
  have ha : LineClassPullbackGroup318.hom (slice τ hτ q) (classOf A)=
      classOf (translatedLine τ hτ q) := by
    change LineSheafPullback318.pullback (slice τ hτ q)
      (LineSheafPullback318.pullback (PELOriginalAdditionSchemeMorphism318.addition τ hτ)
        (classOf L))=_
    rw [←LineClassPullbackLaws318.pullback_composition,slice_addition]
    rfl
  have hb : LineClassPullbackGroup318.hom (slice τ hτ q) (classOf B)=classOf L := by
    change LineSheafPullback318.pullback (slice τ hτ q)
      (LineSheafPullback318.pullback (first τ hτ) (classOf L))=_
    rw [←LineClassPullbackLaws318.pullback_composition,slice_first,
      LineClassPullbackLaws318.pullback_identity]
  rw [ha,hb]
  exact (class_formula τ hτ q).symm

/-- Universal test-scheme formula, including NONREDUCED tests. The
family is pulled back along the actual pair of morphisms, and the two
resulting line factors retain those exact source maps. -/
@[expose] def testIso {T : Scheme} (a b : T ⟶ candidate τ hτ)
    (h : a ≫ π τ hτ=b ≫ π τ hτ) :
    (LineSheafPullback318.line (pullback.lift a b h) (family τ hτ)).object ≅
    (LineSheafTensor318.line
      (LineSheafPullback318.line
        (PELOriginalSchemeAdditionOperations318.combine τ hτ a b h)
        (PELOriginalAlgebraicPolarizationLine318.line τ hτ))
      (FramedLineInverse318.inverse (LineSheafPullback318.line a
        (PELOriginalAlgebraicPolarizationLine318.line τ hτ)))).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  change LineClassPullbackGroup318.hom (pullback.lift a b h)
    (classOf (family τ hτ)) = _
  rw [family,LineSheafClassGroup318.classOf_tensor,
    LineSheafClassGroup318.classOf_inverse,map_mul,map_inv,
    LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse]
  have hfirst : pullback.lift a b h ≫ first τ hτ=a := pullback.lift_fst _ _ _
  change LineSheafPullback318.pullback (pullback.lift a b h)
      (LineSheafPullback318.pullback (PELOriginalAdditionSchemeMorphism318.addition τ hτ)
        (classOf (PELOriginalAlgebraicPolarizationLine318.line τ hτ))) *
    (LineSheafPullback318.pullback (pullback.lift a b h)
      (LineSheafPullback318.pullback (first τ hτ)
        (classOf (PELOriginalAlgebraicPolarizationLine318.line τ hτ))))⁻¹ = _
  rw [←LineClassPullbackLaws318.pullback_composition,
    ←LineClassPullbackLaws318.pullback_composition,hfirst]
  rfl

/-- The zero parameter has a genuinely trivial WHOLE line sheaf.
No choice of rigidification along another section is asserted. -/
@[expose] def zeroFiberIso :
    (LineSheafPullback318.line (slice τ hτ 0) (family τ hτ)).object ≅
      SheafOfModules.unit (candidate τ hτ).ringCatSheaf :=
  fiberIso τ hτ 0 ≪≫ Classical.choice
    ((LineSheafUnit318.eq_unitClass_iff (differenceLine τ hτ 0)).mp
      (zero_class τ hτ))
end PELOriginalTranslationDifferenceFamily318
