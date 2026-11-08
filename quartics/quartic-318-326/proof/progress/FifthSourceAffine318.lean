module
public import FifthCharacterSource318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FifthSourceAffine318
open Polynomial CategoryTheory AlgebraicGeometry
open FifthCharacterSource318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def map:Spec (CommRingCat.of Source)⟶Spec (CommRingCat.of Quartic):=
  Spec.map (CommRingCat.ofHom toSource.toRingHom)
instance map_finite:IsFinite map:=(IsFinite.SpecMap_iff _).mpr toSource_finite
theorem map_surjective:Function.Surjective map:=
  toSource_finite.to_isIntegral.comap_surjective toSource_injective
@[reassoc] theorem over_t:
    map≫Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Quartic))=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Source)):=by
  rw [map,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact toSource.commutes
@[reassoc] theorem over_Q:
    map≫Spec.map (CommRingCat.ofHom (algebraMap ℚ Quartic))=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Source)):=by
  rw [map,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (toSource.restrictScalars ℚ).commutes
end FifthSourceAffine318
