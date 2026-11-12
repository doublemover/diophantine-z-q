module
public import RelativeAmbientReassociationInverse318
public section
noncomputable section
namespace RelativeClassCoefficientComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassQuotient318 RelativeLineClassBaseChange318
universe u
variable {C S R B T : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S) (b : B ⟶ R)
local notation "q" => pullback.snd p r
local notation "e" => RelativeAmbientReassociation318.comparison p r b
/-- Original relative classes over a coefficient-changed curve are
sent to the original absolute-base test by the ACTUAL reassociation. -/
@[expose] def toOriginal : TestClass q b →* TestClass p (b ≫ r) :=
  RelativeLineClassQuotient318.map (pullback.snd q b) (pullback.snd p (b ≫ r))
    e.inv (𝟙 B) (by rw [Category.comp_id]; exact RelativeAmbientReassociationInverse318.second p r b)
lemma on_class (L : LineSheafClass318.Class (pullback q b)) :
    toOriginal p r b (classMap (pullback.snd q b) L)=
      classMap (pullback.snd p (b ≫ r)) (LineClassPullbackHom318.pullback e.inv L) := rfl
lemma natural (t : T ⟶ R) (j : T ⟶ B) (hj : j ≫ b=t) :
    (toOriginal p r t).comp (testMap q b t j hj)=
      (testMap p (b ≫ r) (t ≫ r) j (by rw [←Category.assoc,hj])).comp (toOriginal p r b) := by
  ext x
  obtain ⟨L,rfl⟩ := classMap_surjective (pullback.snd q b) x
  change classMap (pullback.snd p (t ≫ r))
    (LineClassPullbackHom318.pullback (RelativeAmbientReassociation318.comparison p r t).inv
      (LineClassPullbackHom318.pullback (RelativeSchemeCoefficient318.map q b t j hj) L))=
    classMap (pullback.snd p (t ≫ r))
      (LineClassPullbackHom318.pullback (RelativeSchemeCoefficient318.map p (b ≫ r) (t ≫ r) j _)
        (LineClassPullbackHom318.pullback e.inv L))
  rw [←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,
    ←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,
    RelativeAmbientReassociationInverse318.natural]
end RelativeClassCoefficientComparison318
