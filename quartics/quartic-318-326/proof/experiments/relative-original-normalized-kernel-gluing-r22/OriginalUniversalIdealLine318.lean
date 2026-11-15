module
public import RegularSectionDualIdeal318
public import OriginalUniversalPrincipalRegular318
public section
noncomputable section
namespace OriginalUniversalIdealLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A : CommRingCat.{u}) [Algebra R A] (L : Line (Spec A))
local instance : Module R (OriginalLineAffineModel318.sections A L) := Module.compHom _ (algebraMap R A)
variable (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  (ρ : P →ₗ[R] OriginalLineAffineModel318.sections A L)
  (hg : Submodule.span A (Set.range ρ)=⊤)
  (r : OriginalPrincipalAffineFrames318.Index A L)
local notation "B" => OriginalPrincipalAffineFrames318.ring A L r
local notation "f" => OriginalPrincipalAffineFrames318.arrow A L r
local notation "N" => LineSheafPullback318.line (Spec.map f) L
local notation "S" => CommRingCat.of (ProjectiveSectionParameter318.algebra R P)
local notation "BS" => OriginalAffineParameterSquare318.target R A B S f
local notation "k" => OriginalAffineParameterSquare318.targetMap R A B S f
local notation "T" => OriginalAffineFrameSquare318.targetLine B BS k N
local notation "s" => OriginalUniversalPrincipalRegular318.section R A L P ρ r
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra
local instance : Algebra B BS := k.hom.toAlgebra

/-- On every member of the produced actual universal parameter cover,
the original line dual is identified with the SAME zero ideal by its
canonical evaluation. No separately chosen generator or abstract line is
substituted, so these maps have the correct overlap-gluing candidate. -/
@[expose] def dualIdeal : Module.Dual BS (OriginalLineAffineModel318.sections BS T) ≃ₗ[BS]
    OriginalAffineSectionZero318.ideal BS T s :=
  RegularSectionDualIdeal318.equivalence BS T
    (OriginalAffineExtendedFrame318.frame B BS k N (OriginalPrincipalAffineFrames318.frame A L r))
    s (OriginalUniversalPrincipalRegular318.regular R A L P ρ r hg)

lemma dualIdeal_value (φ : Module.Dual BS (OriginalLineAffineModel318.sections BS T)) :
    (dualIdeal R A L P ρ hg r φ).val=φ s := rfl
end OriginalUniversalIdealLine318
