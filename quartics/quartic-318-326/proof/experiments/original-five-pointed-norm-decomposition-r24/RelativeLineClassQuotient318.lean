module
public import LineClassPullbackHom318
public import Mathlib.GroupTheory.QuotientGroup.Defs
public section
noncomputable section
namespace RelativeLineClassQuotient318
open AlgebraicGeometry CategoryTheory
open LineClassPullbackHom318
universe u
variable {X S X' S' X'' S'' : Scheme.{u}}

/-- Exactly the subgroup of original line classes pulled back from the base. -/
@[expose] def baseLines (p : X ⟶ S) : Subgroup (LineSheafClass318.Class X) :=
  (pullback p).range

/-- The naive relative line-class group. This is not its fppf sheafification,
the degree-zero part, or a representing Picard scheme. -/
@[expose] def RelativeClass (p : X ⟶ S) :=
  LineSheafClass318.Class X ⧸ baseLines p

instance relativeCommGroup (p : X ⟶ S) : CommGroup (RelativeClass p) :=
  inferInstanceAs (CommGroup (LineSheafClass318.Class X ⧸ baseLines p))

@[expose] def classMap (p : X ⟶ S) : LineSheafClass318.Class X →* RelativeClass p :=
  QuotientGroup.mk' (baseLines p)

lemma classMap_surjective (p : X ⟶ S) : Function.Surjective (classMap p) :=
  QuotientGroup.mk'_surjective (baseLines p)

lemma classMap_eq_one_iff (p : X ⟶ S) (c : LineSheafClass318.Class X) :
    classMap p c = 1 ↔ ∃ d : LineSheafClass318.Class S, pullback p d = c := by
  exact QuotientGroup.eq_one_iff c

lemma base_class_trivial (p : X ⟶ S) (d : LineSheafClass318.Class S) :
    classMap p (pullback p d) = 1 :=
  (classMap_eq_one_iff p _).2 ⟨d, rfl⟩

/-- A commuting scheme square sends an actual base line to the actual pulled
base line. This is the exact relation needed to descend pullback to quotients. -/
lemma preserves_base (p : X ⟶ S) (p' : X' ⟶ S') (a : X' ⟶ X) (b : S' ⟶ S)
    (square : a ≫ p = p' ≫ b) :
    baseLines p ≤ (baseLines p').comap (pullback a) := by
  rintro c ⟨d, rfl⟩
  refine ⟨pullback b d, ?_⟩
  calc
    pullback p' (pullback b d) = pullback (p' ≫ b) d :=
      (LineClassPullbackLaws318.pullback_composition p' b d).symm
    _ = pullback (a ≫ p) d := congrArg (fun m => pullback m d) square.symm
    _ = pullback a (pullback p d) :=
      LineClassPullbackLaws318.pullback_composition a p d

/-- Actual pullback on naive relative line-class groups for any commuting
scheme square. In particular no flatness or reducedness premise is inserted. -/
@[expose] def map (p : X ⟶ S) (p' : X' ⟶ S') (a : X' ⟶ X) (b : S' ⟶ S)
    (square : a ≫ p = p' ≫ b) : RelativeClass p →* RelativeClass p' :=
  QuotientGroup.map (baseLines p) (baseLines p') (pullback a)
    (preserves_base p p' a b square)

lemma map_class (p : X ⟶ S) (p' : X' ⟶ S') (a : X' ⟶ X) (b : S' ⟶ S)
    (square : a ≫ p = p' ≫ b) (c : LineSheafClass318.Class X) :
    map p p' a b square (classMap p c) = classMap p' (pullback a c) := rfl

lemma map_identity (p : X ⟶ S) (square : (𝟙 X) ≫ p = p ≫ (𝟙 S)) :
    map p p (𝟙 X) (𝟙 S) square = MonoidHom.id (RelativeClass p) := by
  ext c
  obtain ⟨d, rfl⟩ := classMap_surjective p c
  change classMap p (pullback (𝟙 X) d) = classMap p d
  rw [LineClassPullbackHom318.identity]
  rfl

lemma map_composition (p : X ⟶ S) (p' : X' ⟶ S') (p'' : X'' ⟶ S'')
    (a : X' ⟶ X) (b : S' ⟶ S) (a' : X'' ⟶ X') (b' : S'' ⟶ S')
    (square : a ≫ p = p' ≫ b) (square' : a' ≫ p' = p'' ≫ b')
    (compositeSquare : (a' ≫ a) ≫ p = p'' ≫ (b' ≫ b)) :
    map p p'' (a' ≫ a) (b' ≫ b) compositeSquare =
      (map p' p'' a' b' square').comp (map p p' a b square) := by
  ext c
  obtain ⟨d, rfl⟩ := classMap_surjective p c
  change classMap p'' (pullback (a' ≫ a) d) =
    classMap p'' (pullback a' (pullback a d))
  rw [LineClassPullbackHom318.composition]
  rfl
end RelativeLineClassQuotient318
