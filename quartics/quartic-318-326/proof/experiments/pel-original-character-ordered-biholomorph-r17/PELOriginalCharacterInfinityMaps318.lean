module
public import FourRootCharacterInfinityOpen318
public import PELOriginalOrderedCharacterSchemeMaps318
public section
noncomputable section
namespace PELOriginalCharacterInfinityMaps318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterSchemeMaps318
open PELOriginalOrderedCharacterCoordinate318
open FourRootCharacterInfinityOpen318

abbrev indices (i:Fin 4):Fin 3→Fin 4:=SourceTwistArithmetic318.complement i
abbrev Open (i:Fin 4):=OpenRing branches (indices i)

/-- A genuine morphism of whole infinity-neighborhood coordinate rings,
for the SAME ordered Legendre coefficients used by the four-row invariant
consumer. The open retains every original point over infinity. -/
@[expose] def mapOnRings (i:Fin 4):
    InfinityChart318.Ring
      (NormalizedLegendreProjectiveModel318.A (parameter i))
      (NormalizedLegendreProjectiveModel318.B (parameter i))→ₐ[ℂ]Open i:=by
  have hr:=FourRootCharacterInfinityOpen318.square branches (indices i)
  simpa only [PELOriginalOrderedCharacterSchemeMaps318.parameter_eq] using
    ThreeBranchLegendreInfinityAlgebra318.infinityMap
      (branch i 0) (branch i 1) (branch i 2) (branches 0) (first_difference i)
      (u branches (indices i)) (rootUnit branches (indices i)) hr

@[expose] def morphism (i:Fin 4):Spec (CommRingCat.of (Open i))⟶
    NormalizedLegendreProjectiveModel318.model (parameter i):=
  Spec.map (CommRingCat.ofHom (mapOnRings i).toRingHom)≫
    WeierstrassGluing318.infinityChart
      (NormalizedLegendreProjectiveModel318.A (parameter i))
      (NormalizedLegendreProjectiveModel318.B (parameter i))

/-- The structure map is still the original complex coefficient map. -/
lemma over_complex (i:Fin 4):morphism i≫
    NormalizedLegendreProjectiveModel318.structure (parameter i)=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Open i))):=by
  rw [morphism,Category.assoc,WeierstrassGluing318.infinityChart_structure]
  unfold InfinitySmooth318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (mapOnRings i).commutes z

/-- This includes ALL eight original infinity points: the original ratio
signs are not collapsed in the source, but each cubic character map has
the one actual elliptic origin as its image. -/
lemma every_infinity_point (i:Fin 4)
    (f:FourRootInfinityCoordinateRing318.Ring branches→ₐ[ℂ]ℂ)
    (hu:f (FourRootInfinityCoordinateRing318.coordinate branches none)=0):
    (pointLift branches (indices i) f hu).comp (mapOnRings i)=
      InfinityChart318.origin
        (NormalizedLegendreProjectiveModel318.A (parameter i))
        (NormalizedLegendreProjectiveModel318.B (parameter i)):=by
  have h:=ThreeBranchLegendreInfinityAlgebra318.point_at_infinity
    (branch i 0) (branch i 1) (branch i 2) (branches 0) (first_difference i)
    (u branches (indices i)) (rootUnit branches (indices i))
    (FourRootCharacterInfinityOpen318.square branches (indices i))
    (pointLift branches (indices i) f hu) (pointLift_u branches (indices i) f hu)
  simpa only [mapOnRings,PELOriginalOrderedCharacterSchemeMaps318.parameter_eq] using h

/-- The actual point statement is retained after inclusion into the
independent proper Legendre model, not just as two zero coordinates. -/
lemma point_scheme_square (i:Fin 4)
    (f:FourRootInfinityCoordinateRing318.Ring branches→ₐ[ℂ]ℂ)
    (hu:f (FourRootInfinityCoordinateRing318.coordinate branches none)=0):
    Spec.map (CommRingCat.ofHom (pointLift branches (indices i) f hu).toRingHom)≫
      morphism i=
    Spec.map (CommRingCat.ofHom (InfinityChart318.origin
      (NormalizedLegendreProjectiveModel318.A (parameter i))
      (NormalizedLegendreProjectiveModel318.B (parameter i))).toRingHom)≫
      WeierstrassGluing318.infinityChart
        (NormalizedLegendreProjectiveModel318.A (parameter i))
        (NormalizedLegendreProjectiveModel318.B (parameter i)):=by
  rw [morphism,←Category.assoc,←Spec.map_comp]
  exact congrArg (fun h:InfinityChart318.Ring
      (NormalizedLegendreProjectiveModel318.A (parameter i))
      (NormalizedLegendreProjectiveModel318.B (parameter i))→ₐ[ℂ]ℂ=>
      Spec.map (CommRingCat.ofHom h.toRingHom)≫
        WeierstrassGluing318.infinityChart
          (NormalizedLegendreProjectiveModel318.A (parameter i))
          (NormalizedLegendreProjectiveModel318.B (parameter i)))
    (every_infinity_point i f hu)
end PELOriginalCharacterInfinityMaps318
