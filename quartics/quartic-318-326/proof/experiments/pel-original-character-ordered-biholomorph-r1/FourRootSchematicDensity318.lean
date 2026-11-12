module
public import FourRootWholeSchemeGeometry318
public import SchematicEqualityExtension318
public section
noncomputable section
namespace FourRootSchematicDensity318
open AlgebraicGeometry CategoryTheory
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
include hb

/-- The actual original finite chart is schematically dense in the whole
independently glued source, not just dense among complex points. -/
theorem finite_dominant:IsDominant (FourRootGluedScheme318.finiteChart b):=by
  letI:=FourRootWholeSchemeGeometry318.integral b hb
  letI:=FourRootActualGenericField318.affine_domain b hb
  letI:Nonempty (FourRootGluedScheme318.finiteScheme b):=by
    change Nonempty (Spec (CommRingCat.of (FourRootAffineCoordinateRing318.Ring b)))
    infer_instance
  exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (FourRootGluedScheme318.finiteChart b).isOpenEmbedding.isOpenMap⟩

theorem finite_schematic:IsSchemeTheoreticallyDominant (FourRootGluedScheme318.finiteChart b):=by
  letI:=FourRootWholeSchemeGeometry318.integral b hb
  letI:=finite_dominant b hb
  exact IsSchemeTheoreticallyDominant.of_isDominant (FourRootGluedScheme318.finiteChart b)

/-- Equality of actual relative morphisms to a separated target extends
from this exact finite chart to the entire original source. -/
theorem ext {Y Z:Scheme} {f g:FourRootGluedScheme318.scheme b⟶Y}
    (s:Y⟶Z) [IsSeparated s] (hs:f≫s=g≫s)
    (hf:FourRootGluedScheme318.finiteChart b≫f=FourRootGluedScheme318.finiteChart b≫g):f=g:=by
  letI:=finite_schematic b hb
  exact SchematicEqualityExtension318.ext s hs (FourRootGluedScheme318.finiteChart b) hf
end FourRootSchematicDensity318
