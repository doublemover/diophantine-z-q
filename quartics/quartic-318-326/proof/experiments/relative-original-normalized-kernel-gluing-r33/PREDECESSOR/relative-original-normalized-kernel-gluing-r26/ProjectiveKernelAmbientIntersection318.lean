module
public import ProjectiveKernelOverlapSchemes318
public import ProjectiveParameterSliceGluing318
public import CompatibleClosedChartIntersection318
public section
noncomputable section
namespace ProjectiveKernelAmbientIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "tr" => ProjectiveParameterSliceSchemes318.transitionIso R P
local notation "u" => ProjectiveParameterSliceGluing318.into R P
local notation "q" => ProjectiveKernelOverlapAlgebras318.sliceInto R P Q d
/-- Actual old normalized-projective overlap square from its native
GlueData colimit, with the original transition orientation. -/
lemma ambient (i j : Fin F.size) : IsPullback (inc i j) ((tr i j).hom ≫ inc j i) (u i) (u j) := by
  exact IsPullback.of_isLimit ((ProjectiveParameterSliceGluing318.data R P).vPullbackConeIsLimit i j)
@[expose] def ambientMap (i : Fin F.size) : Spec (CommRingCat.of (C i)) ⟶
    ProjectiveParameterSliceGluing318.scheme R P := q i ≫ u i
instance mono (i : Fin F.size) : Mono (ambientMap R P Q d i) := by unfold ambientMap;infer_instance
local notation "a" => ProjectiveKernelOverlapAlgebras318.left R P Q d
local notation "b" => ProjectiveKernelOverlapSchemes318.right R P Q d
local notation "w" => ProjectiveKernelOverlapAlgebras318.into R P Q d
/-- Exact overlap identification for the full normalized kernel charts. -/
lemma intersection (i j : Fin F.size) : IsPullback (a i j) (b i j)
    (ambientMap R P Q d i) (ambientMap R P Q d j) :=
  CompatibleClosedChartIntersection318.intersection (u i) (u j) (inc i j) ((tr i j).hom ≫ inc j i)
    (ambient R P i j) (q i) (q j) (a i j) (b i j) (w i j)
    (ProjectiveKernelOverlapAlgebras318.cartesian R P Q d i j)
    (ProjectiveKernelOverlapSchemes318.right_cartesian R P Q d i j)
instance first_open (i j : Fin F.size) : IsOpenImmersion
    (pullback.fst (ambientMap R P Q d i) (ambientMap R P Q d j)) :=
  CompatibleClosedChartIntersection318.first_open (u i) (u j) (inc i j) ((tr i j).hom ≫ inc j i)
    (ambient R P i j) (q i) (q j) (a i j) (b i j) (w i j)
    (ProjectiveKernelOverlapAlgebras318.cartesian R P Q d i j)
    (ProjectiveKernelOverlapSchemes318.right_cartesian R P Q d i j)
lemma restriction (i j : Fin F.size) : IsPullback
    (pullback.snd (ambientMap R P Q d i) (ambientMap R P Q d j))
    (pullback.fst (ambientMap R P Q d i) (ambientMap R P Q d j) ≫ q i)
    (ambientMap R P Q d j) (u i) :=
  CompatibleClosedChartIntersection318.actual_restriction (u i) (u j) (inc i j) ((tr i j).hom ≫ inc j i)
    (ambient R P i j) (q i) (q j) (a i j) (b i j) (w i j)
    (ProjectiveKernelOverlapAlgebras318.cartesian R P Q d i j)
    (ProjectiveKernelOverlapSchemes318.right_cartesian R P Q d i j)

end ProjectiveKernelAmbientIntersection318
