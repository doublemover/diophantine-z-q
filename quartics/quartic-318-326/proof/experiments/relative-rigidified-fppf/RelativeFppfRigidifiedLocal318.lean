module
public import RelativeSectionNaturality318
public import RelativeFppfLineLocal318
public section
noncomputable section
namespace RelativeFppfRigidifiedLocal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeFppfLineSheaf318 RelativeFppfLineLocal318 RelativeLineClassQuotient318
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X)

/-- The canonical fppf class of an actual line rigidified along the actual
base-changed section. The map forgets the rigidification through the original
relative quotient and the exact sheafification unit. -/
@[expose] def rigidifiedImage (section_eq : e ≫ p = 𝟙 S) (T : Over S)
    (L : RelativeRigidifiedLine318.RigidifiedLine
      (RelativeSectionBaseChange318.sectionOn p e section_eq T.hom)) :
    (sheaf p).obj.obj (op T) := lineImage p T L.line

lemma local_rigidified_iff (section_eq : e ≫ p = 𝟙 S)
    {T V : Over S} (s : (sheaf p).obj.obj (op T)) (g : V ⟶ T) :
    Presheaf.imageSieve (unit p) s g ↔
      ∃ L : RelativeRigidifiedLine318.RigidifiedLine
          (RelativeSectionBaseChange318.sectionOn p e section_eq V.hom),
        rigidifiedImage p e section_eq V L = (sheaf p).obj.map g.op s := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨L, hL⟩ := RelativeSectionBaseChange318.rigidified_representatives_on
      p e section_eq V.hom c
    refine ⟨L, ?_⟩
    change (unit p).app (op V)
      (classMap (pullback.snd p V.hom) (LineSheafClass318.classOf L.line)) = _
    exact (congrArg ((unit p).app (op V)) hL).trans hc
  · rintro ⟨L, hL⟩
    exact ⟨classMap (pullback.snd p V.hom) (LineSheafClass318.classOf L.line), hL⟩

/-- This exact sieve, whose arrows have the original rigidified-object
description above, is fppf covering for every associated-sheaf section. -/
lemma local_rigidified_cover (T : Over S) (s : (sheaf p).obj.obj (op T)) :
    Presheaf.imageSieve (unit p) s ∈ topology S T :=
  local_original_lines_cover p T s
end RelativeFppfRigidifiedLocal318
