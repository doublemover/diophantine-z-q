module
public import AffineAwayPullback318
public import ProjectiveParameterSliceTripleCocycle318
public import ProjectiveParameterSliceSchemes318
public section
noncomputable section
namespace ProjectiveParameterSliceTriplePullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "T" => ProjectiveParameterSliceTripleAlgebra318.algebra R P
variable (i j k : Fin F.size)
local notation "f" => CommRingCat.ofHom (algebraMap (B i) (O i j))
local notation "x" => ProjectiveParameterSliceLocalization318.coordinate R P i k
abbrev scheme : Scheme := Spec (CommRingCat.of (T i j k))

/-- The two maps from the LITERAL triple localization to the actual
pairwise overlap schemes, preserving the original coordinate labels. -/
@[expose] def first : scheme R P i j k ⟶ ProjectiveParameterSliceSchemes318.overlap R P i j :=
  Spec.map (AffineAwayPullback318.targetMap f x)
@[expose] def second : scheme R P i j k ⟶ ProjectiveParameterSliceSchemes318.overlap R P i k :=
  Spec.map (AffineAwayPullback318.arrow f x)

/-- The actual represented triple algebra is precisely the scheme
intersection required by GlueData, not a separate model with a guessed
point bijection. Both projection maps are those of the actual localizations. -/
lemma cartesian : IsPullback (first R P i j k) (second R P i j k)
    (ProjectiveParameterSliceSchemes318.inclusion R P i j)
    (ProjectiveParameterSliceSchemes318.inclusion R P i k) :=
  AffineAwayPullback318.pullback f x

@[expose] def comparison : scheme R P i j k ≅
    pullback (ProjectiveParameterSliceSchemes318.inclusion R P i j)
      (ProjectiveParameterSliceSchemes318.inclusion R P i k) :=
  (cartesian R P i j k).isoPullback
@[reassoc] lemma comparison_fst : (comparison R P i j k).hom ≫ pullback.fst _ _=first R P i j k :=
  (cartesian R P i j k).isoPullback_hom_fst
@[reassoc] lemma comparison_snd : (comparison R P i j k).hom ≫ pullback.snd _ _=second R P i j k :=
  (cartesian R P i j k).isoPullback_hom_snd

instance first_open : IsOpenImmersion (first R P i j k) :=
  MorphismProperty.of_isPullback (cartesian R P i j k).flip inferInstance
instance second_open : IsOpenImmersion (second R P i j k) :=
  MorphismProperty.of_isPullback (cartesian R P i j k) inferInstance
end ProjectiveParameterSliceTriplePullback318
