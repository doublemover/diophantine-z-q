module
public import AffineHOnePointedDeformation318
public import ActualSourceHOnePresentation318
public import OriginalFivePointedDeformations318
public import CompletedCharacterProper318
public import FifthCompletedProper318
public section
noncomputable section
namespace OriginalHOnePointedMaps318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open ContactRelativeLinePresheaf318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral units
/-- The original whole contact H1 now maps to ACTUAL pointed first-order lines
on the original contact scheme, through its original finite/infinity cover. -/
@[expose] def source : ActualSourceHOnePullbacks318.SourceHOne → OriginalFivePointedDeformations318.SourceClass :=
  AffineHOnePointedDeformation318.map sourceStructure
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    ActualSourceHOnePresentation318.cover
lemma source_boundary (x : Γ(ActualSourceHOnePresentation318.Source,
    ActualSourceHOnePresentation318.finiteOpen ⊓ ActualSourceHOnePresentation318.infinityOpen)) :
    source (ActualSourceHOnePresentation318.boundary x) =
      AffineHOnePointedDeformation318.representativeClass sourceStructure
        ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
        ActualSourceHOnePresentation318.cover x :=
  AffineHOnePointedDeformation318.map_boundary _ _ _ _ _ _ x
abbrev finiteOpen (A B : ℚ) : (WeierstrassGluing318.scheme A B).Opens :=
  (WeierstrassGluing318.finiteChart A B).opensRange
abbrev infinityOpen (A B : ℚ) : (WeierstrassGluing318.scheme A B).Opens :=
  (WeierstrassGluing318.infinityChart A B).opensRange
lemma target_cover (A B : ℚ) : finiteOpen A B ⊔ infinityOpen A B = ⊤ := by
  apply top_unique
  intro x _
  rcases WeierstrassGluing318.charts_cover A B x with h | h
  · exact Or.inl h
  · exact Or.inr h
@[expose] def weierstrass (A B : ℚ) [IsIntegral (WeierstrassGluing318.scheme A B)] :
    SheafCohomologyRetraction318.structureH (WeierstrassGluing318.scheme A B) 1 →
      DualNumberScheme318.Class ℚ (WeierstrassGluing318.structureMap A B) :=
  AffineHOnePointedDeformation318.map (WeierstrassGluing318.structureMap A B)
    (finiteOpen A B) (infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B)) (target_cover A B)
local instance characterIntegral (a : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target a) :=
  (CompletedCharacterProper318.target_proper_integral a).2
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target := FifthCompletedProper318.target_proper_integral.2
/-- Every original character target H1 class gets its actual pointed deformation. -/
@[expose] def character (a : Fin 4) :
    SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1 →
      OriginalFivePointedDeformations318.CharacterClass a := weierstrass (publishedA a) (publishedB a)
/-- The same construction on the original full-root target, retaining its exact coefficients. -/
@[expose] def fifth : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1 →
    OriginalFivePointedDeformations318.FifthClass :=
  weierstrass FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
end OriginalHOnePointedMaps318
