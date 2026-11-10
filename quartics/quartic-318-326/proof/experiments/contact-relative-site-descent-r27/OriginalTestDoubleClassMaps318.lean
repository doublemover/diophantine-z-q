module
public import OriginalTestNerveEvaluation318
public section
noncomputable section
namespace OriginalTestDoubleClassMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeLineClassQuotient318
open ActualOverlapDiagram318 OriginalTestCechCoordinates318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b')
abbrev db := OriginalTestDoubleIso318.base b' g
include hg in
lemma second_base : second g ≫ b' = db b' g :=
  (base_equal b b' g hg (first g) (second g) (edge_condition g)).symm

lemma iso_first : (OriginalTestDoubleIso318.iso q b b' g hg).hom ≫
    totalMap q b' (db b' g) (first g) rfl = first (f q b b' g hg) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,totalMap_fst,OriginalTestDoubleIso318.hom_fst]
  · simp only [Category.assoc,totalMap_snd,OriginalTestDoubleIso318.hom_snd_assoc,
      OriginalTestCechCoordinates318.double_first]
lemma iso_second : (OriginalTestDoubleIso318.iso q b b' g hg).hom ≫
    totalMap q b' (db b' g) (second g) (second_base b b' g hg) = second (f q b b' g hg) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,totalMap_fst,OriginalTestDoubleIso318.hom_fst,double_fst_equal]
  · simp only [Category.assoc,totalMap_snd,OriginalTestDoubleIso318.hom_snd_assoc,
      OriginalTestCechCoordinates318.double_second]

lemma iso_square : (OriginalTestDoubleIso318.iso q b b' g hg).hom ≫ pullback.snd q (db b' g) =
    doubleProjection q b b' g hg ≫ 𝟙 (Double g) := by
  rw [Category.comp_id]
  exact OriginalTestDoubleIso318.iso_projection q b b' g hg

/-- Original relative pullback along the exact full-test presentation of
this actual double, over the identity of the original base double. -/
@[expose] def comparison : TestClass q (db b' g) →* RelativeClass (doubleProjection q b b' g hg) :=
  RelativeLineClassQuotient318.map (pullback.snd q (db b' g)) (doubleProjection q b b' g hg)
    (OriginalTestDoubleIso318.iso q b b' g hg).hom (𝟙 _) (iso_square q b b' g hg)

lemma first_comparison :
    RelativeCechClassEffectivity318.firstMap (f q b b' g hg) g (p q b) (p' q b')
      (totalMap_snd q b b' g hg) =
    (comparison q b b' g hg).comp (testMap q b' (db b' g) (first g) rfl) := by
  have h := RelativeLineClassQuotient318.map_composition (p' q b') (pullback.snd q (db b' g))
    (doubleProjection q b b' g hg) (totalMap q b' (db b' g) (first g) rfl) (first g)
    (OriginalTestDoubleIso318.iso q b b' g hg).hom (𝟙 _) (totalMap_snd q b' (db b' g) (first g) rfl)
    (iso_square q b b' g hg) (by
      rw [iso_first,Category.id_comp]
      exact (OriginalTestCechCoordinates318.double_first q b b' g hg).symm)
  simpa only [iso_first,Category.id_comp] using h

lemma second_comparison :
    RelativeCechClassEffectivity318.secondMap (f q b b' g hg) g (p q b) (p' q b')
      (totalMap_snd q b b' g hg) =
    (comparison q b b' g hg).comp
      (testMap q b' (db b' g) (second g) (second_base b b' g hg)) := by
  have h := RelativeLineClassQuotient318.map_composition (p' q b') (pullback.snd q (db b' g))
    (doubleProjection q b b' g hg)
    (totalMap q b' (db b' g) (second g) (second_base b b' g hg)) (second g)
    (OriginalTestDoubleIso318.iso q b b' g hg).hom (𝟙 _)
    (totalMap_snd q b' (db b' g) (second g) (second_base b b' g hg))
    (iso_square q b b' g hg) (by
      rw [iso_second,Category.id_comp]
      exact (OriginalTestCechCoordinates318.double_second q b b' g hg).symm)
  simpa only [iso_second,Category.id_comp] using h

lemma matching (c : TestClass q b')
    (hc : testMap q b' (db b' g) (first g) rfl c =
      testMap q b' (db b' g) (second g) (second_base b b' g hg) c) :
    RelativeCechClassEffectivity318.firstMap (f q b b' g hg) g (p q b) (p' q b')
        (totalMap_snd q b b' g hg) c =
      RelativeCechClassEffectivity318.secondMap (f q b b' g hg) g (p q b) (p' q b')
        (totalMap_snd q b b' g hg) c := by
  rw [first_comparison,second_comparison]
  exact congrArg (comparison q b b' g hg) hc
end OriginalTestDoubleClassMaps318
