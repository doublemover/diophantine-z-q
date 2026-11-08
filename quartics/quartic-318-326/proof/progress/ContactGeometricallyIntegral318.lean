module
public import SourceGeometricallyIntegral318
public import GeometricIntegralDenseOpen318
public import ContactGlobalSmooth318
public section
noncomputable section
namespace ContactGeometricallyIntegral318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)

/-- The actual global normalization of the original contact cover is
geometrically integral over Q. Its full scalar extension, not a chosen
component, is detected by the actual schematically dense source chart. -/
theorem model_geometricallyIntegral : GeometricallyIntegral
    (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ):=by
  let f: (ContactProjectiveModel318.coverMap c).normalization⟶Spec (CommRingCat.of ℚ):=
    (ContactProjectiveModel318.coverMap c).fromNormalization≫ProjectiveJLine318.structureMap ℚ
  let i:=SourceGlobalAffine318.chartEmbedding c
  have hi:i≫f=Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (ContactKummerOrder318.SourceOrder c))):=
    SourceGlobalAffine318.chartEmbedding_over_Q c
  letI:IsDomain (ContactKummerOrder318.SourceOrder c):=ContactKummerOrder318.source_domain c
  letI:IsIntegral (ContactProjectiveModel318.coverMap c).normalization:=
    (ContactGlobalProper318.proper_integral_extension c).2.1
  letI:IsProper f:=(ContactGlobalProper318.proper_integral_extension c).2.2
  letI:QuasiCompact (i≫f):=by rw [hi];infer_instance
  letI:QuasiCompact i:=QuasiCompact.of_comp i f
  letI:GeometricallyIntegral (i≫f):=by
    rw [hi]
    exact SourceGeometricallyIntegral318.source_geometricallyIntegral c
  exact GeometricIntegralDenseOpen318.of_dense_open i f

/-- All properties refer to the same actual Q-structure map and the same
full original normalization. No abstract replacement or component choice. -/
theorem smooth_proper_geometricallyIntegral_model :
    Smooth (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ)∧
    IsProper (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ)∧
    GeometricallyIntegral (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ):=
  ⟨ContactGlobalSmooth318.model_smooth c,
    (ContactGlobalProper318.proper_integral_extension c).2.2,model_geometricallyIntegral c⟩
end ContactGeometricallyIntegral318
