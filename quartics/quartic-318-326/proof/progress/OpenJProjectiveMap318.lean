module
public import JLineOverlap318
public import OpenJIntegralModel318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace OpenJProjectiveMap318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The literal open integral j-line inside the actual proper projective line. -/
@[expose] def baseOpen (N:ℕ) : Spec (CommRingCat.of (OpenJModel318.Base N)) ⟶
    ProjectiveJLine318.scheme ℤ :=
  OpenJIntegralModel318.baseOpen N ≫ JLineAtlas318.chart ℤ 1

instance baseOpen_open (N:ℕ) : IsOpenImmersion (baseOpen N) := by
  unfold baseOpen OpenJIntegralModel318.baseOpen
  infer_instance

/-- Exact integral-base structure map of the open j-line. -/
theorem baseOpen_over_Z (N:ℕ) : baseOpen N ≫ ProjectiveJLine318.structureMap ℤ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (OpenJModel318.Base N))) := by
  rw [baseOpen,Category.assoc,JLineAtlas318.chart_over_base]
  unfold OpenJIntegralModel318.baseOpen
  rw [←Spec.map_comp]
  congr 1

/-- The inverse-coordinate factorization is equality of genuine scheme maps. -/
theorem baseOpen_at_infinity (N:ℕ) : baseOpen N =
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (↑((OpenJModel318.base_units N).2.2.2.1.unit)⁻¹:
        OpenJModel318.Base N)).toRingHom) ≫ JLineAtlas318.chart ℤ 0 :=
  JLineOverlap318.openJ_chart_overlap N

variable (N:ℕ) (B:Type) [CommRing B] [Algebra (OpenJModel318.Base N) B]

/-- An actual open-j algebra gives an actual map to the proper j-line. -/
@[expose] def coverMap : Spec (CommRingCat.of B) ⟶ ProjectiveJLine318.scheme ℤ :=
  Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) B)) ≫ baseOpen N

/-- The actual cover also lands in the inverse j-coordinate chart. -/
theorem coverMap_at_infinity : coverMap N B =
    Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) B)) ≫
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (↑((OpenJModel318.base_units N).2.2.2.1.unit)⁻¹:
        OpenJModel318.Base N)).toRingHom) ≫ JLineAtlas318.chart ℤ 0 := by
  rw [coverMap,baseOpen_at_infinity]

/-- Genuine cover composition is finite type and separated when the actual
open algebra is finite. No moduli or primitive-torsion existence is assumed. -/
theorem coverMap_finite_type [Module.Finite (OpenJModel318.Base N) B] :
    LocallyOfFiniteType (coverMap N B) ∧ IsSeparated (coverMap N B) ∧
    QuasiCompact (coverMap N B) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (OpenJModel318.Base N) B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  unfold coverMap
  exact ⟨inferInstance,inferInstance,inferInstance⟩

instance coverMap_quasiCompact [Module.Finite (OpenJModel318.Base N) B] :
    QuasiCompact (coverMap N B) := (coverMap_finite_type N B).2.2
instance coverMap_separated [Module.Finite (OpenJModel318.Base N) B] :
    IsSeparated (coverMap N B) := (coverMap_finite_type N B).2.1

/-- The concrete actual open-j cover embeds openly into its actual global
normalization over the constructed proper projective line. -/
theorem coverMap_normalization_open [Module.Finite (OpenJModel318.Base N) B] :
    IsOpenImmersion (coverMap N B).toNormalization := by
  letI : LocallyOfFiniteType (coverMap N B) := (coverMap_finite_type N B).1
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap (OpenJModel318.Base N) B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : LocallyQuasiFinite (coverMap N B) := by unfold coverMap; infer_instance
  infer_instance

end OpenJProjectiveMap318
