module
public import ContactKernelOverlapOpenRebuild318
public import SchemeCompatibleOpenUnionRebuild318
public section
noncomputable section
namespace ContactKernelGlobalTargetOpenRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318 ContactOriginalSectionKernel318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance : Module.Finite R (zeroTerm R c L) := (projective_terms R c L).1.1
local instance : Module.Projective R (zeroTerm R c L) := (projective_terms R c L).1.2
local instance : Module.Finite R (oneTerm R c L) := (projective_terms R c L).2.1
local instance : Module.Projective R (oneTerm R c L) := (projective_terms R c L).2.2
local notation "P" => zeroTerm R c L
local notation "Q" => oneTerm R c L
local notation "d" => boundary R c L
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "Z" => ContactOriginalNormalizedKernelScheme318.scheme R c L
local notation "U" => ProjectiveKernelNormalizedGluing318.cover R P Q d
local notation "V" => ContactKernelSliceOpenRebuild318.sliceLocus R c L
local notation "a" => ProjectiveKernelOverlapAlgebras318.left R P Q d
local notation "b" => ProjectiveKernelOverlapSchemes318.right R P Q d
include R c L in
/-- The previously produced full ambient intersection is also the true
intersection in the SAME glued normalized kernel, by monomorphic cancellation. -/
lemma chart_cartesian (i j : Fin F.size) : IsPullback (a i j) (b i j) (U.f i) (U.f j) := by
  apply SchemeMonoPullbackCancellationRebuild318.square
    (ProjectiveKernelNormalizedGluing318.closedInto R P Q d)
  simpa only [ProjectiveKernelNormalizedGluing318.into_closedInto] using
    ProjectiveKernelAmbientIntersection318.intersection R P Q d i j
/-- The genuine GLOBAL descended target open, not a supplied invariant
subfunctor or a new quotient scheme. -/
def locus : Z.Opens := SchemeCompatibleOpenUnionRebuild318.locus U V
abbrev scheme : Scheme := (locus R c L).toScheme
abbrev into : scheme R c L ⟶ Z := (locus R c L).ι
lemma preimage (i : Fin F.size) : U.f i ⁻¹ᵁ locus R c L=V i :=
  SchemeCompatibleOpenUnionRebuild318.preimage U V
    (ProjectiveKernelOverlapAlgebras318.scheme R P Q d) a b
    (chart_cartesian R c L) (ContactKernelOverlapOpenRebuild318.agreement R c L) i
lemma unique (W : Z.Opens) (hW : ∀ i,U.f i ⁻¹ᵁ W=V i) : W=locus R c L :=
  SchemeCompatibleOpenUnionRebuild318.unique U V W hW
end ContactKernelGlobalTargetOpenRebuild318
