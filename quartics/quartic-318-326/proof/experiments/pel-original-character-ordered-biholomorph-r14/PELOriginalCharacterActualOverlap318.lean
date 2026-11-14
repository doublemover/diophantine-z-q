module
public import PELOriginalOrderedCharacterCoordinates318
public import PELOriginalCharacterInfinityMaps318
public import ThreeBranchLegendreReciprocalComparison318
public import WeierstrassActualChartComparison318
public section
noncomputable section
namespace PELOriginalCharacterActualOverlap318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinates318
open PELOriginalOrderedCharacterSchemeMaps318
open PELOriginalCharacterInfinityMaps318
set_option maxHeartbeats 1000000
abbrev I:=FourRootInfinityCoordinateRing318.Ring branches
abbrev N (i:Fin 4):=PELOriginalCharacterInfinityMaps318.Open i
abbrev O (i:Fin 4):=Localization.Away (FourRootCharacterInfinityOpen318.u branches (indices i))

@[expose] def fromNeighborhood (i:Fin 4):N i→ₐ[ℂ]O i:=IsScalarTower.toAlgHom ℂ (N i) (O i)
@[expose] def base (i:Fin 4):I→ₐ[ℂ]O i:=
  (fromNeighborhood i).comp (IsScalarTower.toAlgHom ℂ I (N i))
@[expose] def uUnit (i:Fin 4):(O i)ˣ:=
  (IsLocalization.Away.isUnit_of_dvd
    (FourRootCharacterInfinityOpen318.u branches (indices i)) (dvd_refl _):
    IsUnit (algebraMap (N i) (O i) (FourRootCharacterInfinityOpen318.u branches (indices i)))).unit
lemma uUnit_val (i:Fin 4):(uUnit i:O i)=
    base i (FourRootInfinityCoordinateRing318.coordinate branches none):=by
  exact (IsLocalization.Away.isUnit_of_dvd
    (FourRootCharacterInfinityOpen318.u branches (indices i)) (dvd_refl _):
    IsUnit (algebraMap (N i) (O i) (FourRootCharacterInfinityOpen318.u branches (indices i)))).unit_spec
@[expose] def rootUnit (i:Fin 4):(O i)ˣ:=Units.map (fromNeighborhood i).toMonoidHom
  (FourRootCharacterInfinityOpen318.rootUnit branches (indices i))
lemma rootUnit_val (i:Fin 4):(rootUnit i:O i)=
    base i (FourRootCharacterInfinityOpen318.denominator branches (indices i)):=by
  change fromNeighborhood i (FourRootCharacterInfinityOpen318.rootUnit branches (indices i):N i)=_
  rw [FourRootCharacterInfinityOpen318.rootUnit_val]
  rfl

/-- The original actual overlap algebra maps into the second localization;
the old affine/infinity coordinate transition is retained literally. -/
@[expose] def sourceOverlap (i:Fin 4):FourRootCoordinateOverlap318.InfinityOverlap branches→ₐ[ℂ]O i:=
  IsLocalization.Away.liftAlgHom (f:=base i)
    (FourRootInfinityCoordinateRing318.coordinate branches none) (by
      rw [←uUnit_val]
      exact (uUnit i).isUnit)
lemma source_on_ring (i:Fin 4) (x:I):sourceOverlap i
    (algebraMap I (FourRootCoordinateOverlap318.InfinityOverlap branches) x)=base i x:=by
  simp only [sourceOverlap,IsLocalization.Away.liftAlgHom_apply]
lemma source_inverse (i:Fin 4):sourceOverlap i (FourRootCoordinateOverlap318.ui branches)=(↑(uUnit i)⁻¹:O i):=by
  have h:=congrArg (sourceOverlap i) (FourRootCoordinateOverlap318.u_ui branches)
  simp only [map_mul,map_one,FourRootCoordinateOverlap318.u,source_on_ring,←uUnit_val] at h
  calc
    _=((↑(uUnit i)⁻¹:O i)*(uUnit i:O i))*sourceOverlap i
      (FourRootCoordinateOverlap318.ui branches):=by rw [Units.inv_mul,one_mul]
    _=(↑(uUnit i)⁻¹:O i)*((uUnit i:O i)*sourceOverlap i
      (FourRootCoordinateOverlap318.ui branches)):=by ring
    _=(↑(uUnit i)⁻¹:O i):=by rw [h,mul_one]

@[expose] def fromFinite (i:Fin 4):FourRootAffineCoordinateRing318.Ring branches→ₐ[ℂ]O i:=
  (sourceOverlap i).comp (FourRootCoordinateOverlap318.toInfinityBase branches)
lemma fromFinite_t (i:Fin 4):fromFinite i (FourRootAffineCoordinateRing318.coordinate branches none)=
    algebraMap ℂ (O i) (branches 0)+(↑(uUnit i)⁻¹:O i)^2:=by
  simp only [fromFinite,AlgHom.comp_apply,FourRootCoordinateOverlap318.toInfinityBase_t,
    map_add,map_pow,AlgHom.commutes,source_inverse]
lemma fromFinite_z (i:Fin 4) (k:Fin 4):fromFinite i
    (FourRootAffineCoordinateRing318.coordinate branches (some k))=
      base i (FourRootInfinityCoordinateRing318.coordinate branches (some k))*(↑(uUnit i)⁻¹:O i):=by
  simp only [fromFinite,AlgHom.comp_apply,FourRootCoordinateOverlap318.toInfinityBase_z,
    map_mul,FourRootCoordinateOverlap318.s,source_on_ring,source_inverse]

@[expose] def finiteTarget (i:Fin 4):Target i→ₐ[ℂ]O i:=
  (fromFinite i).comp (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i)
@[expose] def infinityTarget (i:Fin 4):InfinityChart318.Ring (A i) (B i)→ₐ[ℂ]O i:=
  (fromNeighborhood i).comp (PELOriginalCharacterInfinityMaps318.mapOnRings i)

lemma finite_x (i:Fin 4):finiteTarget i (ShortAffineJacobian318.x (A i) (B i))=
    algebraMap ℂ (O i) (difference i)⁻¹*
      (algebraMap ℂ (O i) (branches 0)+(↑(uUnit i)⁻¹:O i)^2-algebraMap ℂ (O i) (center i)):=by
  simp only [finiteTarget,AlgHom.comp_apply,PELOriginalOrderedCharacterCoordinates318.finite_x,
    map_mul,map_sub,AlgHom.commutes,fromFinite_t]
lemma finite_y (i:Fin 4):finiteTarget i (ShortAffineJacobian318.y (A i) (B i))=
    algebraMap ℂ (O i) (PELOriginalOrderedCharacterCoordinates318.rootScale i)⁻¹*
      (rootUnit i:O i)*(↑(uUnit i)⁻¹:O i)^3:=by
  rw [finiteTarget,AlgHom.comp_apply,PELOriginalOrderedCharacterCoordinates318.finite_y_three]
  simp only [map_mul,AlgHom.commutes,fromFinite_z]
  rw [rootUnit_val]
  simp only [FourRootCharacterInfinityOpen318.denominator,map_mul]
  ring

@[expose] def scale (i:Fin 4):ℂ:=
  ThreeBranchLegendreInfinityAlgebra318.scale (branch i 0) (branch i 1)
lemma infinity_x (i:Fin 4):infinityTarget i (InfinityChart318.x (A i) (B i))=
    algebraMap ℂ (O i) (scale i)*(uUnit i:O i)*
      (1+algebraMap ℂ (O i) (branches 0-center i)*(uUnit i:O i)^2)*(↑(rootUnit i)⁻¹:O i):=by
  change fromNeighborhood i ((PELOriginalCharacterInfinityMaps318.mapOnRings i)
    (InfinityChart318.x (A i) (B i)))=_
  rw [uUnit_val]
  simp only [PELOriginalCharacterInfinityMaps318.mapOnRings,
    PELOriginalOrderedCharacterSchemeMaps318.parameter_eq,
    ThreeBranchLegendreInfinityAlgebra318.infinityMap,InfinityChart318.lift_x,
    map_mul,map_add,map_one,map_pow,AlgHom.commutes]
  rfl
lemma infinity_z (i:Fin 4):infinityTarget i (InfinityChart318.z (A i) (B i))=
    algebraMap ℂ (O i) (scale i)^3*(uUnit i:O i)^3*(↑(rootUnit i)⁻¹:O i):=by
  change fromNeighborhood i ((PELOriginalCharacterInfinityMaps318.mapOnRings i)
    (InfinityChart318.z (A i) (B i)))=_
  rw [uUnit_val]
  simp only [PELOriginalCharacterInfinityMaps318.mapOnRings,
    PELOriginalOrderedCharacterSchemeMaps318.parameter_eq,
    ThreeBranchLegendreInfinityAlgebra318.infinityMap,InfinityChart318.lift_z,
    map_mul,map_pow,AlgHom.commutes]
  rfl

/-- Exact coordinate compatibility on the actual twice-localized
intersection. All denominators are constructed units of this very ring. -/
theorem coordinate_compatibility (i:Fin 4):
    infinityTarget i (InfinityChart318.x (A i) (B i))=
      finiteTarget i (ShortAffineJacobian318.x (A i) (B i))*
        infinityTarget i (InfinityChart318.z (A i) (B i)) ∧
    finiteTarget i (ShortAffineJacobian318.y (A i) (B i))*
      infinityTarget i (InfinityChart318.z (A i) (B i))=1:=by
  rw [infinity_x,infinity_z,finite_x,finite_y]
  exact ThreeBranchLegendreReciprocalComparison318.coordinate_identities
    (branch i 0) (branch i 1) (branch i 2) (branches 0) (first_difference i)
    (uUnit i) (rootUnit i)

/-- The previously constructed finite and infinity maps agree as
Scheme morphisms on the actual explicit common localization. -/
theorem target_scheme_square (i:Fin 4):
    Spec.map (CommRingCat.ofHom (finiteTarget i).toRingHom)≫
      WeierstrassGluing318.finiteChart (A i) (B i)=
    Spec.map (CommRingCat.ofHom (infinityTarget i).toRingHom)≫
      WeierstrassGluing318.infinityChart (A i) (B i):=
  WeierstrassActualChartComparison318.scheme_square (A i) (B i)
    (finiteTarget i) (infinityTarget i) (coordinate_compatibility i).1 (coordinate_compatibility i).2
end PELOriginalCharacterActualOverlap318
