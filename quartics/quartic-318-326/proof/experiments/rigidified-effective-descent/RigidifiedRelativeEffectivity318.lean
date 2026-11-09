module
public import RigidifiedIsoEffectivity318
public section
noncomputable section
namespace RigidifiedRelativeEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open RigidifiedOriginalDescentData318 RigidifiedRelativeClass318 RelativeLineClassQuotient318
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (pointed : e' ≫ f = g ≫ e)
  [IsAffineHom f] [Flat f] [Surjective f]
  [IsAffineHom g] [Flat g] [Surjective g]
  (D : Datum f g e e' pointed)
  (p : X ⟶ S) (p' : X' ⟶ S') (square : f ≫ p = p' ≫ g)

/-- The descended rigidified object recovers the original relative class
through the original relative pullback map, before any sheafification.
This is effectiveness for supplied actual descent data, not representability. -/
lemma relative_pullback :
    RelativeLineClassQuotient318.map p p' f g square
      (relativeClass p e (RigidifiedEffectiveDescent318.line f g e e' pointed D)) =
    relativeClass p' e' (localLine f g e e' pointed D) := by
  rw [← RigidifiedPointedPullback318.relativeClass_line e e' f g pointed p p' square]
  exact congrArg (classMap p') (LineSheafClass318.classOf_eq
    (RigidifiedEffectiveDescent318.comparison f g e e' pointed D).iso)

/-- Existence in the unchanged relative quotient retains an actual
rigidified representative and the exact original covering comparison. -/
theorem effective_relative : ∃ L : RelativeRigidifiedLine318.RigidifiedLine e,
    RelativeLineClassQuotient318.map p p' f g square (relativeClass p e L) =
      relativeClass p' e' (localLine f g e e' pointed D) :=
  ⟨RigidifiedEffectiveDescent318.line f g e e' pointed D,
    relative_pullback f g e e' pointed D p p' square⟩
end RigidifiedRelativeEffectivity318
