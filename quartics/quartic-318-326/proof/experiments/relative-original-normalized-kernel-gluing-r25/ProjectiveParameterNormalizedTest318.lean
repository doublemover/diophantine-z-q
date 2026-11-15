module
public import ProjectiveParameterOverlapSchemePoints318
public section
noncomputable section
namespace ProjectiveParameterNormalizedTest318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (S : CommRingCat.{0}) [Algebra R S] (a : A →ₐ[R] S)

@[expose] def slice (i : Fin F.size) (u : Sˣ) (hi : a (x i)=(u:S)) :
    ProjectiveParameterUnitSlice318.SlicePoint R P S i :=
  ProjectiveParameterUnitSlice318.normalize R P S i ⟨a,u,hi⟩
@[expose] def sliceMap (i : Fin F.size) (u : Sˣ) (hi : a (x i)=(u:S)) :=
  ProjectiveParameterSliceAlgebra318.backward R P i S (slice R P S a i u hi)
@[expose] def map (i : Fin F.size) (u : Sˣ) (hi : a (x i)=(u:S)) :
    Spec S ⟶ ProjectiveParameterSliceGluing318.scheme R P :=
  Spec.map (CommRingCat.ofHom (sliceMap R P S a i u hi).toRingHom) ≫
    ProjectiveParameterSliceGluing318.into R P i

variable (i j : Fin F.size) (u v : Sˣ) (hi : a (x i)=(u:S)) (hj : a (x j)=(v:S))
@[expose] def overlap : ProjectiveParameterSliceOverlap318.Point R P S i j where
  point := (slice R P S a i u hi).val
  first_eq := (slice R P S a i u hi).property
  secondUnit := u⁻¹*v
  second_eq := ProjectiveParameterSliceOverlap318.transformed_coordinate R P S a j u v hj

lemma transition_slice : (ProjectiveParameterSliceOverlap318.transition R P S i j
    (overlap R P S a i j u v hi hj)).point=(slice R P S a j v hj).val :=
  ProjectiveParameterSliceOverlap318.triple R P S a u v

/-- Normalizing the SAME original affine parameter at either invertible
coordinate gives exactly the SAME scheme morphism into the glued
projective parameter. This is valid on all coefficient rings, not just
geometric points or a set of scalar orbits. -/
theorem independent : map R P S a i u hi=map R P S a j v hj := by
  have he := ProjectiveParameterOverlapSchemePoints318.into_eq R P i j S
    (overlap R P S a i j u v hi hj)
  have hs : ProjectiveParameterSliceOverlapPoints318.sliceMap R P j i S
      (ProjectiveParameterSliceOverlap318.transition R P S i j (overlap R P S a i j u v hi hj))=
      sliceMap R P S a j v hj := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro z
    rw [ProjectiveParameterSliceOverlapPoints318.sliceMap_mk]
    change (ProjectiveParameterSliceOverlap318.transition R P S i j
      (overlap R P S a i j u v hi hj)).point z=
      Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ z)
    rw [Ideal.Quotient.lift_mk,transition_slice]
  rw [hs] at he
  exact he
end ProjectiveParameterNormalizedTest318
