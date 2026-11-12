module
public import OriginalBaseTwistRemoval318
public import RelativeClassBaseTwistIso318
public import FppfOpenCoverExt318
public section
noncomputable section
namespace OriginalRelativeLocalAbsoluteEquality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 Opposite
variable {X S : Scheme.{0}} (p : X ⟶ S) (B : Over S)
local notation "P" => OriginalAbsoluteLinePresheaf318.presheaf p
local notation "Q" => OriginalAbsoluteLinePresheaf318.quotient p
/-- Equality in the naive relative quotient implies absolute equality
on the actual covering opens of ONE constructed base line. Thus the
absolute equality sieve is genuinely fppf-covering; global equality is
NOT inferred from a relative equality. -/
lemma covering (x y : P.obj (op B)) (h : Q.app (op B) x=Q.app (op B) y) :
    Presheaf.equalizerSieve x y ∈ RelativeFppfLineSheaf318.topology S B := by
  revert h
  induction x, y using Quotient.inductionOn₂ with
  | h L K =>
    intro h
    obtain ⟨M,⟨e⟩⟩ := (RelativeClassBaseTwistIso318.iff_relative (pullback.snd p B.hom) L K).mp h
    let U := OriginalBaseLineFrameCover318.cover M
    apply (RelativeFppfLineSheaf318.topology S).superset_covering _
      (FppfOpenCoverExt318.covering B.hom U)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    change LineClassPullbackHom318.pullback
      (RelativeLineClassBaseChange318.totalMap p B.hom (U.f i ≫ B.hom) (U.f i) rfl) (classOf L)=
      LineClassPullbackHom318.pullback
      (RelativeLineClassBaseChange318.totalMap p B.hom (U.f i ≫ B.hom) (U.f i) rfl) (classOf K)
    exact OriginalBaseTwistRemoval318.classes (pullback.snd p B.hom)
      (pullback.snd p (U.f i ≫ B.hom))
      (RelativeLineClassBaseChange318.totalMap p B.hom (U.f i ≫ B.hom) (U.f i) rfl)
      (U.f i) (RelativeLineClassBaseChange318.totalMap_snd _ _ _ _ _)
      L K M e (OriginalBaseLineFrameCover318.class_one M i)
end OriginalRelativeLocalAbsoluteEquality318
