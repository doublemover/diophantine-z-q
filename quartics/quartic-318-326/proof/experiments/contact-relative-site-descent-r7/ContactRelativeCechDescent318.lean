module
public import OriginalTestDoubleClassMaps318
public import ContactUniversalRigidifiedClass318
public section
noncomputable section
namespace ContactRelativeCechDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeSectionBaseChange318 ActualOverlapDiagram318
open ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T T' : Scheme} (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
  (g : T' ⟶ T) (hg : g ≫ b = b') [IsAffineHom g] [Flat g] [Surjective g]

/-- Matching original relative line classes on the original full Contact
family tests have a unique global class along every affine faithfully flat
base cover. All actual nerve rigidity hypotheses are now proved, not assumed. -/
theorem matching_unique (c : TestClass (q t) b')
    (hc : testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl c =
      testMap (q t) b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
        (OriginalTestDoubleClassMaps318.second_base b b' g hg) c) :
    ∃! d : TestClass (q t) b, testMap (q t) b b' g hg d = c :=
  RelativeCechClassSeparated318.matching_unique (totalMap (q t) b b' g hg) g
    (testSection t b) (testSection t b')
    (sectionOn_naturality (q t) (e t) (section_eq t) b b' g hg)
    (pullback.snd (q t) b) (pullback.snd (q t) b') (totalMap_snd (q t) b b' g hg)
    (sectionOn_snd (q t) (e t) (section_eq t) b) (sectionOn_snd (q t) (e t) (section_eq t) b')
    (test_evaluation_bijective t b')
    (OriginalTestNerveEvaluation318.double_evaluation (q t) (e t) (section_eq t) b b' g hg)
    (OriginalTestNerveEvaluation318.triple_evaluation (q t) (e t) (section_eq t) b b' g hg).injective c
    (OriginalTestDoubleClassMaps318.matching (q t) b b' g hg c hc)

lemma testMap_injective : Function.Injective (testMap (q t) b b' g hg) :=
  RelativeCechClassSeparated318.map_injective (totalMap (q t) b b' g hg) g
    (testSection t b) (testSection t b')
    (sectionOn_naturality (q t) (e t) (section_eq t) b b' g hg)
    (pullback.snd (q t) b) (pullback.snd (q t) b') (totalMap_snd (q t) b b' g hg)
    (sectionOn_snd (q t) (e t) (section_eq t) b) (sectionOn_snd (q t) (e t) (section_eq t) b')
    (test_evaluation_bijective t b')
    (OriginalTestNerveEvaluation318.double_evaluation (q t) (e t) (section_eq t) b b' g hg).injective
end ContactRelativeCechDescent318
