module
public import FiniteOverlapSheaves318
public import InvariantChartForms318
public import WeierstrassGluing318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public section
noncomputable section
namespace ActualInfinityOpen318
open AlgebraicGeometry CategoryTheory
open WeierstrassOverlap318 ActualDifferentialOverlap318 DifferentialChartMaps318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

theorem finiteBase_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (finiteBaseMap A B).toRingHom)) := by
  have h0 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (InfinityOverlap A B) (CommonRing A B)))) :=
    IsOpenImmersion.of_isLocalization (actualJacobian A B*(2*ii A B))
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (toInfinityBase A B).toRingHom)) := by
    rw [←WeierstrassGluing318.intoAffine_eq]
    infer_instance
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((algebraMap (InfinityOverlap A B) (CommonRing A B)).comp (toInfinityBase A B).toRingHom)))
  rw [show CommRingCat.ofHom
      ((algebraMap (InfinityOverlap A B) (CommonRing A B)).comp (toInfinityBase A B).toRingHom) =
    CommRingCat.ofHom (toInfinityBase A B).toRingHom ≫
      CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B)) from rfl,
    Spec.map_comp]
  infer_instance

theorem infinityBase_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (infinityBaseMap A B).toRingHom)) := by
  have h0 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (InfinityOverlap A B) (CommonRing A B)))) :=
    IsOpenImmersion.of_isLocalization (actualJacobian A B*(2*ii A B))
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Infinity A B) (InfinityOverlap A B)))) :=
    IsOpenImmersion.of_isLocalization (InfinityChart318.z A B)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Infinity A B) (CommonRing A B))))
  rw [IsScalarTower.algebraMap_eq (Infinity A B) (InfinityOverlap A B) (CommonRing A B)]
  change IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityOverlap A B)) ≫
      CommRingCat.ofHom (algebraMap (InfinityOverlap A B) (CommonRing A B))))
  rw [Spec.map_comp]
  infer_instance

/-- The actual previously constructed finite differential-chart map is open. -/
theorem finite_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom)) := by
  let f := Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (Affine A B) (FiniteChart A B)))
  have hg : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (ShortAffineJacobian318.presentation A B 1).jacobian
  have heq : f ≫ g=Spec.map (CommRingCat.ofHom (finiteBaseMap A B).toRingHom) := by
    dsimp [f,g]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact finiteChartMap_integral A B
  have hfg : IsOpenImmersion (f ≫ g) := by rw [heq]; exact finiteBase_open A B
  exact IsOpenImmersion.of_comp f g

/-- The actual previously constructed infinity differential-chart map is open. -/
theorem infinity_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom)) := by
  let f := Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (Infinity A B) (InfinityChart A B)))
  have hg : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (InfinityChart318.presentation A B).jacobian
  have heq : f ≫ g=Spec.map (CommRingCat.ofHom (infinityBaseMap A B).toRingHom) := by
    dsimp [f,g]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact infinityChartMap_integral A B
  have hfg : IsOpenImmersion (f ≫ g) := by rw [heq]; exact infinityBase_open A B
  exact IsOpenImmersion.of_comp f g

/-- Actual ring formal étaleness follows from the proved open immersion. -/
theorem finite_formallyEtale (A B : R) :
    letI : Algebra (FiniteChart A B) (CommonRing A B) := (finiteChartMap A B).toRingHom.toAlgebra
    Algebra.FormallyEtale (FiniteChart A B) (CommonRing A B) := by
  letI : Algebra (FiniteChart A B) (CommonRing A B) := (finiteChartMap A B).toRingHom.toAlgebra
  letI := finite_open A B
  have he : (finiteChartMap A B).toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P:=@Etale) (φ:=CommRingCat.ofHom (finiteChartMap A B).toRingHom)).mp inferInstance
  exact he.formallyEtale

theorem infinity_formallyEtale (A B : R) :
    letI : Algebra (InfinityChart A B) (CommonRing A B) := (infinityChartMap A B).toRingHom.toAlgebra
    Algebra.FormallyEtale (InfinityChart A B) (CommonRing A B) := by
  letI : Algebra (InfinityChart A B) (CommonRing A B) := (infinityChartMap A B).toRingHom.toAlgebra
  letI := infinity_open A B
  have he : (infinityChartMap A B).toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P:=@Etale) (φ:=CommRingCat.ofHom (infinityChartMap A B).toRingHom)).mp inferInstance
  exact he.formallyEtale
end ActualInfinityOpen318
