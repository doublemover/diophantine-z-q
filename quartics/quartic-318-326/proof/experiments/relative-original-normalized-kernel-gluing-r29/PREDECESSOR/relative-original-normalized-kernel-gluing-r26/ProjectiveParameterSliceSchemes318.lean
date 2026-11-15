module
public import ProjectiveParameterSliceLocalizationIso318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace ProjectiveParameterSliceSchemes318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P

/-- Actual affine quotient-chart schemes and literal principal overlap
schemes. These are not a substitute curve or an abstract orbit set. -/
abbrev chart (i : Fin F.size) : Scheme := Spec (CommRingCat.of (B i))
abbrev overlap (i j : Fin F.size) : Scheme := Spec (CommRingCat.of (O i j))
@[expose] def inclusion (i j : Fin F.size) : overlap R P i j ⟶ chart R P i :=
  Spec.map (CommRingCat.ofHom (algebraMap (B i) (O i j)))
instance inclusion_open (i j : Fin F.size) : IsOpenImmersion (inclusion R P i j) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway

/-- Scheme transitions are induced by the SAME inverse localized
coordinate algebra maps, with Spec reversing their direction. -/
@[expose] def transitionIso (i j : Fin F.size) : overlap R P i j ≅ overlap R P j i :=
  Scheme.Spec.mapIso
    (ProjectiveParameterSliceLocalizationIso318.equivalence R P i j).toRingEquiv.toCommRingCatIso.op

@[expose] def projection (i : Fin F.size) : chart R P i ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (B i)))
@[expose] def overlapProjection (i j : Fin F.size) : overlap R P i j ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (O i j)))

/-- Every actual principal overlap inclusion is over the original base. -/
@[reassoc] lemma inclusion_projection (i j : Fin F.size) :
    inclusion R P i j ≫ projection R P i=overlapProjection R P i j := by
  rw [inclusion,projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R (B i) (O i j)).symm

/-- The opposite overlap embedding remains over the SAME base as well;
this is the structural compatibility needed for a relative gluing. -/
@[reassoc] lemma transition_projection (i j : Fin F.size) :
    (transitionIso R P i j).hom ≫ overlapProjection R P j i=overlapProjection R P i j := by
  change Spec.map (CommRingCat.ofHom
    (ProjectiveParameterSliceLocalization318.transition R P i j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (O j i)))=_
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (ProjectiveParameterSliceLocalization318.transition R P i j).commutes r

/-- All actual quotient charts have actual open overlap maps and
base-preserving transition isomorphisms. A global scheme still requires
the triple-overlap pullback cocycle, not merely these pairwise data. -/
theorem relative_overlap (i j : Fin F.size) :
    IsOpenImmersion (inclusion R P i j) ∧
    (transitionIso R P i j).hom ≫ inclusion R P j i ≫ projection R P j=
      inclusion R P i j ≫ projection R P i := by
  refine ⟨inferInstance,?_⟩
  rw [inclusion_projection,inclusion_projection,transition_projection]
end ProjectiveParameterSliceSchemes318
