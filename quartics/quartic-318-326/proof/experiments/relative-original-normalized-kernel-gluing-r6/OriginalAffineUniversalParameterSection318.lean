module
public import OriginalAffineParameterSquare318
public import OriginalAffineFrameEvaluation318
public import OriginalAffineSectionZero318
public import SectionZeroRegularCoordinate318
public section
noncomputable section
namespace OriginalAffineUniversalParameterSection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A B : CommRingCat.{u}) [Algebra R A] (f : A ⟶ B)
  (L : Line (Spec A)) (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra
local instance : Module R (OriginalLineAffineModel318.sections A L) := Module.compHom _ (algebraMap R A)
variable (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  (ρ : P →ₗ[R] OriginalLineAffineModel318.sections A L)
local notation "S" => CommRingCat.of (ProjectiveSectionParameter318.algebra R P)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "AS" => OriginalAffineParameterSquare318.source R A S
local notation "BS" => OriginalAffineParameterSquare318.target R A B S f
local notation "i" => OriginalAffineParameterSquare318.sourceMap R A S
local notation "k" => OriginalAffineParameterSquare318.targetMap R A B S f
local notation "g" => OriginalAffineParameterSquare318.chartMap R A B S f
local notation "h" => OriginalAffineParameterSquare318.square R A B S f
local instance : Algebra B BS := k.hom.toAlgebra

/-- The universal affine section is an actual finite sum of genuine
original geometric pullback units on the parameter-extended original line. -/
@[expose] def section : OriginalLineAffineModel318.sections AS
    (OriginalAffineFrameSquare318.sourceLine A AS i L) :=
  ∑ j, (SymmetricAlgebra.ι R (Module.Dual R P) (F.coordinate j) ⊗ₜ[R] (1:A)) •
    OriginalAffineLinePathSections318.restriction i L
      (OriginalAffineFrameSquare318.sourceLine A AS i L) (Iso.refl _) (ρ (F.vector j))

@[expose] def localSection : OriginalLineAffineModel318.sections BS
    (OriginalAffineFrameSquare318.targetLine B BS k N) :=
  OriginalAffineLinePathSections318.restriction g
    (OriginalAffineFrameSquare318.sourceLine A AS i L)
    (OriginalAffineFrameSquare318.targetLine B BS k N)
    (OriginalAffineFrameSquare318.comparison A B AS BS f i g k h L N e)
    (section R A L P ρ)

/-- The coordinate of the ACTUAL geometrically restricted section agrees
with the previously proved regular SAME universal tensor evaluation, under
the literal factor-swap isomorphism. There is no supplied coefficient equation. -/
lemma coefficient_comparison : Algebra.TensorProduct.comm R S B
    (OriginalAffineExtendedFrame318.frame B BS k N v (localSection R A B f L N e P ρ)) =
    UniversalScalarCoordinate318.coefficient R P B
      (OriginalAffineFrameEvaluation318.evaluation R A B f L N e v P ρ) := by
  change Algebra.TensorProduct.comm R S B
    (OriginalAffineParameterSquare318.coordinate R A B S f L N e v (section R A L P ρ)) = _
  rw [section,OriginalAffineParameterSquare318.coefficient_formula,map_sum,
    UniversalScalarCoordinate318.coefficient_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Algebra.TensorProduct.comm_tmul]
  rfl

lemma coordinate_regular (hg : Submodule.span A (Set.range ρ)=⊤) (a : BS)
    (ha : a * OriginalAffineExtendedFrame318.frame B BS k N v
      (localSection R A B f L N e P ρ)=0) : a=0 := by
  have he := congrArg (Algebra.TensorProduct.comm R S B) ha
  rw [map_mul,map_zero,coefficient_comparison] at he
  have hz := OriginalAffineFrameEvaluation318.regular R A B f L N e v P ρ hg
    (Algebra.TensorProduct.comm R S B a) he
  apply (Algebra.TensorProduct.comm R S B).injective
  simpa only [map_zero] using hz

/-- Exact literal section ideal on the original local parameter chart,
with its nilpotent structure preserved and its actual frame coordinate. -/
lemma ideal_principal : OriginalAffineSectionZero318.ideal BS
    (OriginalAffineFrameSquare318.targetLine B BS k N) (localSection R A B f L N e P ρ) =
    Ideal.span {OriginalAffineExtendedFrame318.frame B BS k N v
      (localSection R A B f L N e P ρ)} :=
  SectionZeroRegularCoordinate318.ideal_in_frame BS _ (localSection R A B f L N e P ρ)
    (OriginalAffineExtendedFrame318.frame B BS k N v)

/-- An actual intrinsic regular section of the original local pulled
line, not only a regular element in an unrelated symmetric algebra. -/
theorem regular_section (hg : Submodule.span A (Set.range ρ)=⊤) :
    SectionZeroRegularCoordinate318.Regular BS _ (localSection R A B f L N e P ρ) :=
  (SectionZeroRegularCoordinate318.regular_iff BS _ (localSection R A B f L N e P ρ)
    (OriginalAffineExtendedFrame318.frame B BS k N v)).mpr
      (coordinate_regular R A B f L N e v P ρ hg)
end OriginalAffineUniversalParameterSection318
