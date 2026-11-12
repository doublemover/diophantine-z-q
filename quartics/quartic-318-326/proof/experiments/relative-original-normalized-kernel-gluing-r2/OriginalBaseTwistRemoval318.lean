module
public import OriginalBaseLineFrameCover318
public section
noncomputable section
namespace OriginalBaseTwistRemoval318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X B X' B' : Scheme.{u}} (p : X ⟶ B) (p' : X' ⟶ B')
  (f : X' ⟶ X) (a : B' ⟶ B) (hf : f ≫ p=p' ≫ a)
  (L K : Line X) (M : Line B)
/-- An actual base twist disappears only where its original base line
has been proved trivial. The full original source family is retained. -/
include hf in
lemma classes (e : (LineSheafTensor318.line L (LineSheafPullback318.line p M)).object ≅ K.object)
    (hm : LineClassPullbackHom318.pullback a (classOf M)=1) :
    LineClassPullbackHom318.pullback f (classOf L)=LineClassPullbackHom318.pullback f (classOf K) := by
  have hl : classOf (LineSheafTensor318.line L (LineSheafPullback318.line p M))=classOf K :=
    classOf_eq e
  have he := congrArg (LineClassPullbackHom318.pullback f) hl
  rw [LineSheafClassGroup318.classOf_tensor,map_mul] at he
  have ht : LineClassPullbackHom318.pullback f
      (classOf (LineSheafPullback318.line p M))=1 := by
    change LineClassPullbackHom318.pullback f (LineClassPullbackHom318.pullback p (classOf M))=1
    rw [←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,hf,
      LineClassPullbackHom318.composition,MonoidHom.comp_apply,hm,map_one]
  rw [ht,mul_one] at he
  exact he
/-- The resulting equality is an actual full sheaf isomorphism, with
its original pullback objects, rather than a support or degree equality. -/
include hf in
lemma isomorphism (e : (LineSheafTensor318.line L (LineSheafPullback318.line p M)).object ≅ K.object)
    (hm : LineClassPullbackHom318.pullback a (classOf M)=1) :
    Nonempty ((LineSheafPullback318.line f L).object ≅ (LineSheafPullback318.line f K).object) :=
  (classOf_eq_iff _ _).mp (classes p p' f a hf L K M e hm)
end OriginalBaseTwistRemoval318
