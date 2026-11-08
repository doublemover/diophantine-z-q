module
public import FiniteChartSchematicDensity318
public section
noncomputable section

namespace FiniteChartSchematicDensity318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassGluing318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)
/-- The literal affine chart inclusion is quasi-compact, even over a
non-Noetherian base: its composite with the separated structural map is affine. -/
instance finiteChart_quasiCompact : QuasiCompact (finiteChart A B):=by
  letI:=CubicClosedImmersion318.structure_proper A B
  haveI:QuasiCompact (finiteChart A B≫structureMap A B):=by
    rw [finiteChart_structure]
    unfold ShortAffineScheme318.structureMap
    apply (HasAffineProperty.iff_of_isAffine (P:=@QuasiCompact)
      (Q:=fun X _ _ _ => CompactSpace X)).mpr
    unfold ShortAffineScheme318.scheme
    infer_instance
  exact QuasiCompact.of_comp (finiteChart A B) (structureMap A B)
end FiniteChartSchematicDensity318
