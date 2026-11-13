module
public import ProjectiveKernelAmbientIntersection318
public section
noncomputable section
namespace ProjectiveKernelNormalizedGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
local notation "Z" => fun i : Fin F.size => Spec (CommRingCat.of (C i))
local notation "f" => ProjectiveKernelAmbientIntersection318.ambientMap R P Q d
local notation "q" => ProjectiveKernelOverlapAlgebras318.sliceInto R P Q d
/-- A genuine GLOBAL normalized-kernel scheme, glued using its actual
ambient fiber products. No quotient representability is assumed. -/
abbrev scheme : Scheme := MonoFamilyGlueData318.scheme Z f
abbrev into (i : Fin F.size) : Z i ⟶ scheme R P Q d := MonoFamilyGlueData318.into Z f i
abbrev cover : (scheme R P Q d).OpenCover := MonoFamilyGlueData318.cover Z f
abbrev closedInto : scheme R P Q d ⟶ ProjectiveParameterSliceGluing318.scheme R P :=
  MonoFamilyGlueData318.map Z f
@[reassoc] lemma into_closedInto (i : Fin F.size) :
    into R P Q d i ≫ closedInto R P Q d=f i := MonoFamilyGlueData318.into_map Z f i
/-- Each original affine normalized kernel slice is literally the
restriction of the constructed global scheme to the OLD ambient chart. -/
lemma cartesian (i : Fin F.size) : IsPullback (into R P Q d i) (q i)
    (closedInto R P Q d) (ProjectiveParameterSliceGluing318.into R P i) :=
  SchemeClosedCoverGluing318.cartesian (ProjectiveParameterSliceGluing318.cover R P) Z q
    (ProjectiveKernelAmbientIntersection318.restriction R P Q d) i
instance closed : IsClosedImmersion (closedInto R P Q d) :=
  SchemeClosedCoverGluing318.closed (ProjectiveParameterSliceGluing318.cover R P) Z q
    (ProjectiveKernelAmbientIntersection318.restriction R P Q d)
instance into_open (i : Fin F.size) : IsOpenImmersion (into R P Q d i) := inferInstance
lemma jointly_surjective (x : scheme R P Q d) : ∃ i y,into R P Q d i y=x :=
  (cover R P Q d).exists_eq x
abbrev projection : scheme R P Q d ⟶ Spec R :=
  closedInto R P Q d ≫ ProjectiveParameterSliceBase318.projection R P
/-- Its actual overlaps retain the full quotient ideals, while the
native ambient fiber products supply the triple gluing cocycle. -/
lemma overlap (i j : Fin F.size) : IsPullback
    (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j))
    (into R P Q d i) (into R P Q d j) := MonoFamilyGlueData318.intersection Z f i j

end ProjectiveKernelNormalizedGluing318
