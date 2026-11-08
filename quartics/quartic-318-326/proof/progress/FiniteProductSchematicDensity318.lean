module
public import SchematicProductDensity318
public import FiniteChartQuasiCompact318
public section
noncomputable section
namespace FiniteProductSchematicDensity318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeierstrassGluing318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)

/-- The actual finite-times-finite chart in the actual relative square. -/
@[expose] def pairMap :
    pullback (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)⟶
      pullback (structureMap A B) (structureMap A B):=
  (pullback.congrHom (finiteChart_structure A B).symm (finiteChart_structure A B).symm).hom≫
    SchematicProductDensity318.productMap (finiteChart A B) (finiteChart A B)
      (structureMap A B) (structureMap A B)

@[reassoc] theorem pairMap_fst : pairMap A B≫pullback.fst (structureMap A B) (structureMap A B)=
    pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)≫
      finiteChart A B:=by
  simp [pairMap,Category.assoc,SchematicProductDensity318.productMap_fst,pullback.congrHom]
@[reassoc] theorem pairMap_snd : pairMap A B≫pullback.snd (structureMap A B) (structureMap A B)=
    pullback.snd (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)≫
      finiteChart A B:=by
  simp [pairMap,Category.assoc,SchematicProductDensity318.productMap_snd,pullback.congrHom]
instance pairMap_open : IsOpenImmersion (pairMap A B):=by unfold pairMap;infer_instance
instance pairMap_quasiCompact : QuasiCompact (pairMap A B):=by unfold pairMap;infer_instance

theorem pairMap_dense (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsSchemeTheoreticallyDominant (pairMap A B):=by
  letI:=FiniteChartSchematicDensity318.finiteChart_dense A B
  letI:=structure_smooth A B hD
  unfold pairMap
  infer_instance

/-- Morphisms from the actual completed relative square into a separated
completed cubic are determined on the actual finite product chart. -/
theorem pair_hom_ext_to_completed (A' B':R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:pullback (structureMap A B) (structureMap A B)⟶scheme A' B')
    (hbase:f≫structureMap A' B'=g≫structureMap A' B')
    (hfinite:pairMap A B≫f=pairMap A B≫g):f=g:=by
  letI:=pairMap_dense A B hD
  letI:=CubicClosedImmersion318.structure_proper A' B'
  exact SchematicEqualityExtension318.ext (structureMap A' B') hbase (pairMap A B) hfinite

@[expose] def pairStructure :=pullback.fst (structureMap A B) (structureMap A B)≫structureMap A B
@[expose] def finitePairStructure :=
  pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B)≫
    ShortAffineScheme318.structureMap A B
@[reassoc] theorem pairMap_structure : pairMap A B≫pairStructure A B=finitePairStructure A B:=by
  rw [pairStructure,←Category.assoc,pairMap_fst,Category.assoc,finiteChart_structure]
  rfl

/-- The left-associated actual finite cube in the left-associated completed
relative cube; the bracketing is retained literally. -/
@[expose] def tripleMap :
    pullback (finitePairStructure A B) (ShortAffineScheme318.structureMap A B)⟶
      pullback (pairStructure A B) (structureMap A B):=
  (pullback.congrHom (pairMap_structure A B).symm (finiteChart_structure A B).symm).hom≫
    SchematicProductDensity318.productMap (pairMap A B) (finiteChart A B)
      (pairStructure A B) (structureMap A B)
@[reassoc] theorem tripleMap_fst :
    tripleMap A B≫pullback.fst (pairStructure A B) (structureMap A B)=
      pullback.fst (finitePairStructure A B) (ShortAffineScheme318.structureMap A B)≫pairMap A B:=by
  simp [tripleMap,Category.assoc,SchematicProductDensity318.productMap_fst,pullback.congrHom]
@[reassoc] theorem tripleMap_snd :
    tripleMap A B≫pullback.snd (pairStructure A B) (structureMap A B)=
      pullback.snd (finitePairStructure A B) (ShortAffineScheme318.structureMap A B)≫finiteChart A B:=by
  simp [tripleMap,Category.assoc,SchematicProductDensity318.productMap_snd,pullback.congrHom]
instance tripleMap_open : IsOpenImmersion (tripleMap A B):=by unfold tripleMap;infer_instance
instance tripleMap_quasiCompact : QuasiCompact (tripleMap A B):=by unfold tripleMap;infer_instance

theorem tripleMap_dense (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsSchemeTheoreticallyDominant (tripleMap A B):=by
  letI:=FiniteChartSchematicDensity318.finiteChart_dense A B
  letI:=pairMap_dense A B hD
  letI:=structure_smooth A B hD
  haveI:Flat (pairStructure A B):=by unfold pairStructure;infer_instance
  unfold tripleMap
  infer_instance

theorem triple_hom_ext_to_completed (A' B':R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:pullback (pairStructure A B) (structureMap A B)⟶scheme A' B')
    (hbase:f≫structureMap A' B'=g≫structureMap A' B')
    (hfinite:tripleMap A B≫f=tripleMap A B≫g):f=g:=by
  letI:=tripleMap_dense A B hD
  letI:=CubicClosedImmersion318.structure_proper A' B'
  exact SchematicEqualityExtension318.ext (structureMap A' B') hbase (tripleMap A B) hfinite
end FiniteProductSchematicDensity318
