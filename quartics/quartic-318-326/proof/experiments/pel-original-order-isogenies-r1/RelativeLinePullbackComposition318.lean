module
public import RelativeFppfLineSheaf318
public section
noncomputable section
namespace RelativeLinePullbackComposition318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineFunctorPullback318 RelativeLineClassQuotient318
universe u
variable {X Y Z S : Scheme.{u}} (p : X⟶S) (q : Y⟶S) (r : Z⟶S)
  (f : X⟶Y) (hf : f≫q=p) (g : Y⟶Z) (hg : g≫r=q)
lemma square : (f≫g)≫r=p := by rw [Category.assoc,hg,hf]
lemma baseMap_comp {T : Scheme.{u}} (t : T⟶S) :
    baseMap p r (f≫g) (square p q r f hf g hg) t=
      baseMap p q f hf t≫baseMap q r g hg t := by
  apply pullback.hom_ext <;>
    simp only [baseMap,Category.assoc,pullback.lift_fst,pullback.lift_snd,
      pullback.lift_fst_assoc,pullback.lift_snd_assoc]
lemma relativeMap_comp {T : Scheme.{u}} (t : T⟶S) :
    relativeMap p r (f≫g) (square p q r f hf g hg) t=
      (relativeMap p q f hf t).comp (relativeMap q r g hg t) := by
  ext c
  obtain ⟨d,rfl⟩ := classMap_surjective (pullback.snd r t) c
  change classMap (pullback.snd p t)
      (LineClassPullbackHom318.pullback (baseMap p r (f≫g) _ t) d)=
    classMap (pullback.snd p t)
      (LineClassPullbackHom318.pullback (baseMap p q f hf t)
        (LineClassPullbackHom318.pullback (baseMap q r g hg t) d))
  rw [baseMap_comp]
  simp only [LineClassPullbackHom318.apply_eq]
  rw [LineClassPullbackLaws318.pullback_composition]
/-- Literal contravariant composition on the actual relative presheaf,
proved before sheafification by surjectivity of the genuine quotient. -/
lemma transformation_comp :
    transformation p r (f≫g) (square p q r f hf g hg)=
      transformation q r g hg≫transformation p q f hf := by
  apply NatTrans.ext
  intro T
  exact CommGrpCat.hom_ext (relativeMap_comp p q r f hf g hg T.unop.hom)
/-- The actual fppf pullback has the same contravariant composition law;
this uses the existing sheafification functor, not pointwise descent. -/
lemma fppf_comp :
    RelativeFppfLineSheaf318.pullback p r (f≫g) (square p q r f hf g hg)=
      RelativeFppfLineSheaf318.pullback q r g hg≫
        RelativeFppfLineSheaf318.pullback p q f hf := by
  unfold RelativeFppfLineSheaf318.pullback
  rw [transformation_comp,Functor.map_comp]
end RelativeLinePullbackComposition318
