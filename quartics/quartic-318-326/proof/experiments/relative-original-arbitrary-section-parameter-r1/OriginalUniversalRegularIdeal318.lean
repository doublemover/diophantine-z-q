module
public import OriginalRegularIdealCover318
public section
noncomputable section
namespace OriginalUniversalRegularIdeal318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A : CommRingCat.{u}) [Algebra R A] (L : Line (Spec A))
local instance : Module R (OriginalLineAffineModel318.sections A L) := Module.compHom _ (algebraMap R A)
variable (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  (ρ : P →ₗ[R] OriginalLineAffineModel318.sections A L)
local notation "S" => CommRingCat.of (ProjectiveSectionParameter318.algebra R P)
local notation "AS" => OriginalAffineParameterSquare318.source R A S
local notation "i" => OriginalAffineParameterSquare318.sourceMap R A S
local notation "M" => OriginalAffineFrameSquare318.sourceLine A AS i L

/-- Consume the actual principal cover at the IDEAL of the same universal
section on its whole tensor chart. All local equations are genuine ideal
extensions through original parameter-open maps. -/
theorem property (hg : Submodule.span A (Set.range ρ)=⊤) :
    OriginalRegularIdealCover318.Property AS
      (OriginalAffineSectionZero318.ideal AS M
        (OriginalAffineUniversalParameterSection318.section R A L P ρ)) := by
  intro x
  obtain ⟨r,⟨y,hy⟩,c,hc,hr⟩ :=
    OriginalUniversalPrincipalRegular318.covering_equations R A L P ρ hg x
  let B := OriginalPrincipalAffineFrames318.ring A L r
  let f := OriginalPrincipalAffineFrames318.arrow A L r
  let N := LineSheafPullback318.line (Spec.map f) L
  let BS := OriginalPrincipalParameterCover318.chart R A S L r
  let g := OriginalPrincipalParameterCover318.arrow R A S L r
  refine ⟨BS,g,inferInstance,⟨y,hy⟩,c,?_,hr⟩
  have he := OriginalAffineSectionZero318.along_path g M
    (OriginalAffineFrameSquare318.targetLine B BS
      (OriginalAffineParameterSquare318.targetMap R A B S f) N)
    (OriginalAffineFrameSquare318.comparison A B AS BS f i g
      (OriginalAffineParameterSquare318.targetMap R A B S f)
      (OriginalAffineParameterSquare318.square R A B S f) L N (Iso.refl _))
    (OriginalAffineUniversalParameterSection318.section R A L P ρ)
  exact he.symm.trans hc
end OriginalUniversalRegularIdeal318
