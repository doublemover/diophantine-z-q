module
public import CartesianSourceOpenCover318
public import ContactOriginalNormalizedKernelScheme318
public section
noncomputable section
namespace ProjectiveKernelNonzeroSourceRebuild318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "K" => ProjectiveKernelParameter318.algebra R P Q d
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "W" => ProjectiveParameterPrincipalCover318.locus R P
local notation "U" => ProjectiveParameterPrincipalCover318.cover R P
local notation "Z" => fun i : Fin F.size =>
  Spec (CommRingCat.of (ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i))

/-- The original FULL kernel ideal in the finite-projective term algebra. -/
def ambientInto : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (ProjectiveKernelParameter318.quotient R P Q d).toRingHom)
abbrev source : Scheme := pullback (ambientInto R P Q d) W.ι
abbrev original : source R P Q d ⟶ Spec (CommRingCat.of K) := pullback.fst _ _
abbrev ambient : source R P Q d ⟶ W.toScheme := pullback.snd _ _
instance original_open : IsOpenImmersion (original R P Q d) := inferInstance
def chartAmbient (i : Fin F.size) : Z i ⟶ U.X i :=
  Spec.map (CommRingCat.ofHom
    (ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i).toRingHom)
lemma chart_square (i : Fin F.size) : IsPullback
    (ProjectiveKernelPrincipalCartesian318.into R P Q d i) (chartAmbient R P Q d i)
    (ambientInto R P Q d) (U.f i≫W.ι) := by
  simpa only [ProjectiveParameterPrincipalCover318.into_affine] using
    (ProjectiveKernelPrincipalCartesian318.cartesian R P Q d i).flip
abbrev chart (i : Fin F.size) : Z i ⟶ source R P Q d :=
  CartesianSourceOpenCover318.into (ambientInto R P Q d) W.ι U Z
    (ProjectiveKernelPrincipalCartesian318.into R P Q d)
    (chartAmbient R P Q d) (chart_square R P Q d) i
abbrev cover : (source R P Q d).OpenCover :=
  CartesianSourceOpenCover318.cover (ambientInto R P Q d) W.ι U Z
    (ProjectiveKernelPrincipalCartesian318.into R P Q d)
    (chartAmbient R P Q d) (chart_square R P Q d)
@[reassoc] lemma chart_original (i : Fin F.size) : chart R P Q d i≫original R P Q d=
    ProjectiveKernelPrincipalCartesian318.into R P Q d i :=
  CartesianSourceOpenCover318.source _ _ _ _ _ _ _ i
@[reassoc] lemma chart_ambient (i : Fin F.size) : chart R P Q d i≫ambient R P Q d=
    chartAmbient R P Q d i≫U.f i :=
  CartesianSourceOpenCover318.base _ _ _ _ _ _ _ i
end ProjectiveKernelNonzeroSourceRebuild318
