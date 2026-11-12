module
public import RelativeFamilyFrameRecovery318
public section
noncomputable section
namespace RelativeFamilyFrameEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
lemma rule_ext {F G : RelativeFamilyFrameRule318.Rule p L}
    (h : ∀ (S : CommRingCat.{u}) (b : Spec S ⟶ B),F.app S b=G.app S b) : F=G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      have he : f=g := by funext S b; exact h S b
      cases he
      rfl
/-- Genuine relative affine-test descent over an ARBITRARY base scheme:
whole natural frames on all affine base changes are equivalent to an
actual global frame of the original line on the original total scheme. -/
@[expose] def equivalence : Frames L ≃ RelativeFamilyFrameRule318.Rule p L where
  toFun := RelativeFamilyFrameRule318.ofFrame p L
  invFun := RelativeFamilyFrameRecovery318.frame p L
  left_inv e := RelativeFamilyFrameRecovery318.ofFrame p L e
  right_inv F := by
    apply rule_ext p L
    intro S b
    exact RelativeFamilyFrameRecovery318.family_test p L F S b
/-- The equivalence does not merely recover source-affine restrictions;
it recovers the complete generally NONAFFINE family over each affine base test. -/
lemma actual_family (F : RelativeFamilyFrameRule318.Rule p L) (S : CommRingCat.{u}) (b : Spec S ⟶ B) :
    OriginalFramePullback318.frame (CategoryTheory.Limits.pullback.fst p b) L
      ((equivalence p L).symm F)=F.app S b :=
  RelativeFamilyFrameRecovery318.family_test p L F S b
end RelativeFamilyFrameEquivalence318
