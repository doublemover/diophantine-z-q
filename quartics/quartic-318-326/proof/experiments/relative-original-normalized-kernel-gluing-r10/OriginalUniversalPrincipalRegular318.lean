module
public import OriginalPrincipalParameterCover318
public import OriginalAffineUniversalParameterSection318
public section
noncomputable section
namespace OriginalUniversalPrincipalRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A : CommRingCat.{u}) [Algebra R A] (L : Line (Spec A))
local instance : Module R (OriginalLineAffineModel318.sections A L) := Module.compHom _ (algebraMap R A)
variable (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  (ρ : P →ₗ[R] OriginalLineAffineModel318.sections A L)
  (r : OriginalPrincipalAffineFrames318.Index A L)
local notation "B" => OriginalPrincipalAffineFrames318.ring A L r
local notation "f" => OriginalPrincipalAffineFrames318.arrow A L r
local notation "N" => LineSheafPullback318.line (Spec.map f) L
local notation "S" => CommRingCat.of (ProjectiveSectionParameter318.algebra R P)
local notation "BS" => OriginalAffineParameterSquare318.target R A B S f
local notation "k" => OriginalAffineParameterSquare318.targetMap R A B S f
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra
local instance : Algebra B BS := k.hom.toAlgebra

/-- The local universal section on a produced principal affine frame.
There is no external line trivialization or comparison-isomorphism input. -/
abbrev section := OriginalAffineUniversalParameterSection318.localSection
  R A B f L N (Iso.refl _) P ρ

/-- Regularity on EVERY member of the genuine parameter-pulled principal
frame cover, using the original global generation premise, not a supplied
primitive coordinate or a claimed regular specialized section. -/
theorem regular (hg : Submodule.span A (Set.range ρ)=⊤) :
    SectionZeroRegularCoordinate318.Regular BS
      (OriginalLineAffineModel318.sections BS (OriginalAffineFrameSquare318.targetLine B BS k N))
      (section R A L P ρ r) :=
  OriginalAffineUniversalParameterSection318.regular_section R A B f L N (Iso.refl _)
    (OriginalPrincipalAffineFrames318.frame A L r) P ρ hg

/-- The same literal zero ideal on the actual parameter-open chart is
principal with a proved non-zero-divisor generator. -/
theorem ideal_and_regular (hg : Submodule.span A (Set.range ρ)=⊤) :
    ∃ c : BS, OriginalAffineSectionZero318.ideal BS
      (OriginalAffineFrameSquare318.targetLine B BS k N) (section R A L P ρ r)=Ideal.span {c} ∧
      ∀ a : BS, a*c=0 → a=0 := by
  refine ⟨OriginalAffineExtendedFrame318.frame B BS k N
    (OriginalPrincipalAffineFrames318.frame A L r) (section R A L P ρ r),?_,?_⟩
  · exact OriginalAffineUniversalParameterSection318.ideal_principal R A B f L N (Iso.refl _)
      (OriginalPrincipalAffineFrames318.frame A L r) P ρ
  · exact OriginalAffineUniversalParameterSection318.coordinate_regular R A B f L N (Iso.refl _)
      (OriginalPrincipalAffineFrames318.frame A L r) P ρ hg
/-- The affine universal zero has a genuine open cover by its original
parameter-pulled line frames and a regular principal equation on every
member. This supplies covering AND equations, not only a local criterion. -/
@[expose] def HasCoveringEquations : Prop :=
    ∀ x : Spec (OriginalAffineParameterSquare318.source R A S),
    ∃ r : OriginalPrincipalAffineFrames318.Index A L,
      (∃ y : Spec (OriginalPrincipalParameterCover318.chart R A S L r),
        Spec.map (OriginalPrincipalParameterCover318.arrow R A S L r) y=x) ∧
      ∃ c : OriginalPrincipalParameterCover318.chart R A S L r,
        OriginalAffineSectionZero318.ideal _
          (OriginalAffineFrameSquare318.targetLine _ _
            (OriginalAffineParameterSquare318.targetMap R A _ S
              (OriginalPrincipalAffineFrames318.arrow A L r))
            (LineSheafPullback318.line (Spec.map (OriginalPrincipalAffineFrames318.arrow A L r)) L))
          (section R A L P ρ r)=Ideal.span {c} ∧
        ∀ a, a*c=0 → a=0

theorem covering_equations (hg : Submodule.span A (Set.range ρ)=⊤) :
    HasCoveringEquations R A L P ρ := by
  intro x
  obtain ⟨r,y,hy⟩ := OriginalPrincipalParameterCover318.covers R A S L x
  exact ⟨r,⟨y,hy⟩,ideal_and_regular R A L P ρ r hg⟩
end OriginalUniversalPrincipalRegular318
