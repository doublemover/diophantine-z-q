module
public import RelativeRigidifiedLine318
public import RelativeLineClassBaseChange318
public section
noncomputable section
namespace RelativeSectionBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X S T T' : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X)

/-- An actual section stays a section on every full scheme-theoretic base
change, including nonaffine and nonreduced test schemes. -/
@[expose] def sectionOn (section_eq : e ≫ p = 𝟙 S) (t : T ⟶ S) :
    T ⟶ pullback p t :=
  pullback.lift (t ≫ e) (𝟙 T) (by simp [Category.assoc, section_eq])

@[reassoc] lemma sectionOn_fst (section_eq : e ≫ p = 𝟙 S) (t : T ⟶ S) :
    sectionOn p e section_eq t ≫ pullback.fst p t = t ≫ e :=
  pullback.lift_fst _ _ _

@[reassoc] lemma sectionOn_snd (section_eq : e ≫ p = 𝟙 S) (t : T ⟶ S) :
    sectionOn p e section_eq t ≫ pullback.snd p t = 𝟙 T :=
  pullback.lift_snd _ _ _

lemma sectionOn_naturality (section_eq : e ≫ p = 𝟙 S)
    (t : T ⟶ S) (t' : T' ⟶ S) (a : T' ⟶ T) (ha : a ≫ t = t') :
    sectionOn p e section_eq t' ≫ RelativeLineClassBaseChange318.totalMap p t t' a ha =
      a ≫ sectionOn p e section_eq t := by
  apply pullback.hom_ext <;>
    simp [RelativeLineClassBaseChange318.totalMap, sectionOn, Category.assoc, ← ha]

/-- Every base-test relative class is identified with the kernel of the
original section restriction on that test. This is not the degree-zero part. -/
@[expose] def equivalenceOn (section_eq : e ≫ p = 𝟙 S) (t : T ⟶ S) :
    RelativeLineClassBaseChange318.TestClass p t ≃*
      (LineClassPullbackHom318.pullback (sectionOn p e section_eq t)).ker :=
  RelativeLineSectionNormalization318.equivalence (pullback.snd p t)
    (sectionOn p e section_eq t) (sectionOn_snd p e section_eq t)

lemma rigidified_representatives_on (section_eq : e ≫ p = 𝟙 S) (t : T ⟶ S) :
    Function.Surjective
      (fun L : RelativeRigidifiedLine318.RigidifiedLine (sectionOn p e section_eq t) =>
        RelativeLineClassQuotient318.classMap (pullback.snd p t)
          (LineSheafClass318.classOf L.line)) :=
  RelativeRigidifiedLine318.relativeClass_surjective (pullback.snd p t)
    (sectionOn p e section_eq t) (sectionOn_snd p e section_eq t)
end RelativeSectionBaseChange318
