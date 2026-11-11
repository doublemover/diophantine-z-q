module
public import OriginalTestRefinement318
public section
noncomputable section
namespace ContactFppfCechDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeSectionBaseChange318 ActualOverlapDiagram318
open ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T T' : Scheme} (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
  (g : T' ⟶ T) (hg : g ≫ b = b')

/-- All original Contact test-class matching is effective along any
original arrow supplied with an actual affine faithfully flat refinement. -/
theorem refined_matching_unique (r : ActualAffineBaseRefinement318.Refinement g)
    (c : TestClass (q t) b')
    (hc : testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl c =
      testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
        (OriginalTestDoubleClassMaps318.second_base b b' g hg) c) :
    ∃! d : TestClass (q t) b, testMap (q t) b b' g hg d = c :=
  RelativeRefinedCechEffectivity318.matching_unique (totalMap (q t) b b' g hg) g
    (testSection t b) (testSection t b')
    (sectionOn_naturality (q t) (e t) (section_eq t) b b' g hg)
    (pullback.snd (q t) b) (pullback.snd (q t) b') (totalMap_snd (q t) b b' g hg)
    (sectionOn_snd (q t) (e t) (section_eq t) b) (sectionOn_snd (q t) (e t) (section_eq t) b')
    (OriginalTestRefinement318.refinement (q t) b b' g hg r)
    (test_evaluation_bijective t b')
    (OriginalTestNerveEvaluation318.double_evaluation (q t) (e t) (section_eq t) b b' g hg)
    (OriginalTestNerveEvaluation318.triple_evaluation (q t) (e t) (section_eq t) b b' g hg).injective c
    (OriginalTestDoubleClassMaps318.matching (q t) b b' g hg c hc)

/-- No affine or quasi-compact condition is imposed on the original fppf
covering morphism or its source. The affine test base supplies a genuine
finite affine refinement; original full-test matching has a unique solution. -/
theorem matching_unique [IsAffine T] [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
    (c : TestClass (q t) b')
    (hc : testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl c =
      testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
        (OriginalTestDoubleClassMaps318.second_base b b' g hg) c) :
    ∃! d : TestClass (q t) b, testMap (q t) b b' g hg d = c := by
  letI := AffineBaseFppfDescent318.cover_quasiCompact g
  exact refined_matching_unique t b b' g hg (ActualAffineBaseRefinement318.refinement g) c hc

/-- The analogous fpqc result uses the actual quasi-compact covering
morphism and the same unchanged full-test Čech equation. -/
theorem fpqc_matching_unique [IsAffine T] [Flat g] [Surjective g] [QuasiCompact g]
    (c : TestClass (q t) b')
    (hc : testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl c =
      testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
        (OriginalTestDoubleClassMaps318.second_base b b' g hg) c) :
    ∃! d : TestClass (q t) b, testMap (q t) b b' g hg d = c :=
  refined_matching_unique t b b' g hg (ActualAffineBaseRefinement318.refinement g) c hc
end ContactFppfCechDescent318
