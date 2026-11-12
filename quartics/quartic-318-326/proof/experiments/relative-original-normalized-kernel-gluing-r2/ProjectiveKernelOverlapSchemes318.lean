module
public import ProjectiveKernelOverlapTransitions318
public section
noncomputable section
namespace ProjectiveKernelOverlapSchemes318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
open ProjectiveKernelOverlapAlgebras318
variable (i j : Fin F.size)
@[expose] def transitionIso : scheme R P Q d i j ≅ scheme R P Q d j i :=
  Scheme.Spec.mapIso (ProjectiveKernelOverlapTransitions318.equivalence R P Q d i j).toRingEquiv.toCommRingCatIso.op
/-- The quotient transition is the restriction of the EXACT old
ambient transition, not merely a scalar point bijection. -/
@[reassoc] lemma transition_into : (transitionIso R P Q d i j).hom ≫ into R P Q d j i=
    into R P Q d i j ≫ (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom := by
  change Spec.map (CommRingCat.ofHom (ProjectiveKernelOverlapTransitions318.transition R P Q d i j).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (quotient R P Q d j i).toRingHom)=
    Spec.map (CommRingCat.ofHom (quotient R P Q d i j).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceLocalization318.transition R P i j).toRingHom)
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (ProjectiveKernelOverlapTransitions318.transition_quotient R P Q d i j)
@[expose] def right : scheme R P Q d i j ⟶ Spec (CommRingCat.of (C j)) :=
  (transitionIso R P Q d i j).hom ≫ left R P Q d j i
instance right_open : IsOpenImmersion (right R P Q d i j) := by unfold right;infer_instance
lemma transition_cartesian : IsPullback (transitionIso R P Q d i j).hom
    (into R P Q d i j) (into R P Q d j i)
    (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom :=
  IsPullback.of_horiz_isIso ⟨transition_into R P Q d i j⟩
/-- BOTH exact local closed-family pullback squares are produced. -/
lemma right_cartesian : IsPullback (right R P Q d i j) (into R P Q d i j)
    (sliceInto R P Q d j)
    ((ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom ≫
      ProjectiveParameterSliceSchemes318.inclusion R P j i) :=
  (transition_cartesian R P Q d i j).paste_horiz (cartesian R P Q d j i)

end ProjectiveKernelOverlapSchemes318
