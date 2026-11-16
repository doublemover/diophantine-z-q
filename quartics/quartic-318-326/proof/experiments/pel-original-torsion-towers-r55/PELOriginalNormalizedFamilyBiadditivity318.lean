module
public import PELOriginalNormalizedPolarizationFamily318
public section
noncomputable section
namespace PELOriginalNormalizedFamilyBiadditivity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalPolarizationBicharacter318
open PELOriginalNormalizedPolarizationFamily318 PELOriginalTripleProductReduced318
open PELOriginalTripleComplexPoints318 PELOriginalSchemeGroupAssociativity318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Genuine line isomorphisms on any scheme test, from pullbacks of the
SAME global product family. These are not just equations after taking
a relative quotient or after fppf sheafification. -/
@[expose] def addRightIso {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b c : Points τ hτ Y ρ) :
    (LineSheafPullback318.line (pairMap τ hτ ρ a (b+c)) (family τ hτ)).object ≅
      (LineSheafTensor318.line
        (LineSheafPullback318.line (pairMap τ hτ ρ a b) (family τ hτ))
        (LineSheafPullback318.line (pairMap τ hτ ρ a c) (family τ hτ))).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,pair_class,pair_class,pair_class,add_right]
@[expose] def addLeftIso {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (a b c : Points τ hτ Y ρ) :
    (LineSheafPullback318.line (pairMap τ hτ ρ (a+b) c) (family τ hτ)).object ≅
      (LineSheafTensor318.line
        (LineSheafPullback318.line (pairMap τ hτ ρ a c) (family τ hτ))
        (LineSheafPullback318.line (pairMap τ hτ ρ b c) (family τ hτ))).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,pair_class,pair_class,pair_class,add_left]

@[expose] def x : Points τ hτ (Triple τ hτ) (structureMap τ hτ) :=
  ⟨first τ hτ,first_over τ hτ⟩
@[expose] def y : Points τ hτ (Triple τ hτ) (structureMap τ hτ) :=
  ⟨second τ hτ,second_over τ hτ⟩
@[expose] def z : Points τ hτ (Triple τ hτ) (structureMap τ hτ) :=
  ⟨third τ hτ,third_over τ hτ⟩

/-- Biadditivity holds on the WHOLE triple product. No passage from
independent complex-parameter isomorphisms to a family is made. -/
@[expose] def wholeRightIso := addRightIso τ hτ (structureMap τ hτ) (x τ hτ) (y τ hτ) (z τ hτ)
@[expose] def wholeLeftIso := addLeftIso τ hτ (structureMap τ hτ) (x τ hτ) (y τ hτ) (z τ hτ)

/-- The literal whole-product isomorphism pulls back with BOTH inverse
maps along arbitrary scheme morphisms, including nonreduced tests.
No associativity/interchange coherence for independently chosen
isomorphisms is asserted here. -/
@[expose] def wholeRightTestIso {Y : Scheme} (f : Y ⟶ Triple τ hτ) :=
  (Scheme.Modules.pullback f).mapIso (wholeRightIso τ hτ)
@[expose] def wholeLeftTestIso {Y : Scheme} (f : Y ⟶ Triple τ hτ) :=
  (Scheme.Modules.pullback f).mapIso (wholeLeftIso τ hτ)
lemma wholeRight_hom_inv {Y : Scheme} (f : Y ⟶ Triple τ hτ) :
    (wholeRightTestIso τ hτ f).hom≫(wholeRightTestIso τ hτ f).inv=𝟙 _ :=
  (wholeRightTestIso τ hτ f).hom_inv_id
lemma wholeLeft_hom_inv {Y : Scheme} (f : Y ⟶ Triple τ hτ) :
    (wholeLeftTestIso τ hτ f).hom≫(wholeLeftTestIso τ hτ f).inv=𝟙 _ :=
  (wholeLeftTestIso τ hτ f).hom_inv_id
end PELOriginalNormalizedFamilyBiadditivity318
