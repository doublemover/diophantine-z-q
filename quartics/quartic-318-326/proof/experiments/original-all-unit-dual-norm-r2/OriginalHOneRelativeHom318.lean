module
public import AffineHOnePicardKernelHom318
public section
noncomputable section
namespace OriginalHOneRelativeHom318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 ContactRelativeLinePresheaf318
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ base R) (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤)
/-- The existing naive relative Picard quotient receives a genuine homomorphism
from original H1. Neither fppf sheafification nor representability is inferred. -/
@[expose] def relativeHom : Multiplicative (SheafCohomologyRetraction318.structureH X 1) →*
    RelativeLineClassQuotient318.RelativeClass (pullback.snd p (structureMap R)) :=
  (RelativeLineClassQuotient318.classMap (pullback.snd p (structureMap R))).comp
    (AffineHOnePicardKernelHom318.hom p U V hU hV h)
lemma relativeHom_apply (z : SheafCohomologyRetraction318.structureH X 1) :
    relativeHom p U V hU hV h (Multiplicative.ofAdd z) =
      OriginalFivePointedDeformations318.relativeClass p
        (AffineHOnePointedDeformation318.map p U V hU hV h z) := rfl
variable {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
    (W Z : Y.Opens) (hW : IsAffineOpen W) (hZ : IsAffineOpen Z) (hWZ : W ⊔ Z = ⊤)
    (hu : U ≤ f ⁻¹ᵁ W) (hv : V ≤ f ⁻¹ᵁ Z)
/-- Exact original scheme pullback on H1 matches the original relative-class
pullback, with its original dual-number base change, as a group-law-compatible map. -/
lemma naturality (z : SheafCohomologyRetraction318.structureH Y 1) :
    RelativeLineFunctorPullback318.relativeMap p q f hf (structureMap R)
      (relativeHom q W Z hW hZ hWZ (Multiplicative.ofAdd z)) =
    relativeHom p U V hU hV h
      (Multiplicative.ofAdd (SchemeSourceCohomology318.pullback f 1 z)) := by
  have hh := congrArg (OriginalFivePointedDeformations318.relativeClass p)
    (AffineHOnePointedNaturality318.naturality p q f hf W Z U V hW hZ hU hV hWZ h hu hv z)
  rw [OriginalFivePointedDeformations318.relative_pullback] at hh
  exact hh
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
@[expose] def source : Multiplicative ActualSourceHOnePullbacks318.SourceHOne →*
    RelativeLineClassQuotient318.RelativeClass (pullback.snd sourceStructure (structureMap ℚ)) :=
  relativeHom sourceStructure ActualSourceHOnePresentation318.finiteOpen
    ActualSourceHOnePresentation318.infinityOpen ActualSourceHOnePresentation318.finite_affine
    ActualSourceHOnePresentation318.infinity_affine ActualSourceHOnePresentation318.cover
@[expose] def weierstrass (A B : ℚ) [IsIntegral (WeierstrassGluing318.scheme A B)] :
    Multiplicative (SheafCohomologyRetraction318.structureH (WeierstrassGluing318.scheme A B) 1) →*
    RelativeLineClassQuotient318.RelativeClass
      (pullback.snd (WeierstrassGluing318.structureMap A B) (structureMap ℚ)) :=
  relativeHom (WeierstrassGluing318.structureMap A B)
    (OriginalHOnePointedMaps318.finiteOpen A B) (OriginalHOnePointedMaps318.infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))
    (OriginalHOnePointedMaps318.target_cover A B)
local instance characterIntegral (a : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target a) :=
  (CompletedCharacterProper318.target_proper_integral a).2
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target :=
  FifthCompletedProper318.target_proper_integral.2
@[expose] def character (a : Fin 4) := weierstrass (SourceTwistArithmetic318.publishedA a)
  (SourceTwistArithmetic318.publishedB a)
@[expose] def fifth := weierstrass FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
/-- The exact old four relative pullback maps, not newly assigned maps on labels. -/
lemma character_naturality (a : Fin 4)
    (z : SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1) :
    (ContactRelativeLinePresheaf318.characterPullback a).app (op (Over.mk (structureMap ℚ)))
      (character a (Multiplicative.ofAdd z)) =
      source (Multiplicative.ofAdd (ActualSourceHOnePullbacks318.characterPullback a z)) := by
  have hh := congrArg (OriginalFivePointedDeformations318.relativeClass sourceStructure)
    (OriginalFiveHOnePointedNaturality318.character a z)
  rw [OriginalFivePointedDeformations318.character_matches_relative] at hh
  exact hh
/-- A concrete four-factor sum-to-tensor statement on the SAME canonical
contact source map. This does not silently add the distinct fifth source cover. -/
lemma character_sum
    (z : (a : Fin 4) → SheafCohomologyRetraction318.structureH (CompletedCharacterSchemeMaps318.Target a) 1) :
    source (Multiplicative.ofAdd (∑ a : Fin 4, ActualSourceHOnePullbacks318.characterPullback a (z a))) =
      ∏ a : Fin 4, (ContactRelativeLinePresheaf318.characterPullback a).app
        (op (Over.mk (structureMap ℚ))) (character a (Multiplicative.ofAdd (z a))) := by
  calc
    _ = ∏ a : Fin 4, source (Multiplicative.ofAdd
        (ActualSourceHOnePullbacks318.characterPullback a (z a))) :=
      map_prod source (fun a : Fin 4 => Multiplicative.ofAdd
        (ActualSourceHOnePullbacks318.characterPullback a (z a))) Finset.univ
    _ = _ := Finset.prod_congr rfl (fun a _ => (character_naturality a (z a)).symm)
/-- The fifth square is still stated on the actual adapted source-cover map.
It is not yet a fifth factor in character_sum. -/
lemma fifth_naturality (z : SheafCohomologyRetraction318.structureH FifthCompletedGlobal318.Target 1) :
    ContactRelativeLinePresheaf318.fifthPullback.app (op (Over.mk (structureMap ℚ)))
      (fifth (Multiplicative.ofAdd z)) =
    OriginalFivePointedDeformations318.relativeClass sourceStructure
      (OriginalFiveHOnePointedNaturality318.sourceForFifth (ActualSourceHOnePullbacks318.fifthPullback z)) := by
  have hh := congrArg (OriginalFivePointedDeformations318.relativeClass sourceStructure)
    (OriginalFiveHOnePointedNaturality318.fifth z)
  rw [OriginalFivePointedDeformations318.fifth_matches_relative] at hh
  exact hh
end OriginalHOneRelativeHom318
