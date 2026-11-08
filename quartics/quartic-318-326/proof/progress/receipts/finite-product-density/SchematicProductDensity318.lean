module
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public section
noncomputable section
namespace SchematicProductDensity318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {U V X Y S:Scheme.{u}}

/-- Change the left factor by its actual pullback map. -/
@[expose] def leftMap (i:U⟶X) (f:X⟶S) (g:Y⟶S) :
    pullback (i≫f) g⟶pullback f g:=
  (pullbackRightPullbackFstIso f g i).inv≫pullback.snd i (pullback.fst f g)
@[reassoc] theorem leftMap_fst (i:U⟶X) (f:X⟶S) (g:Y⟶S) :
    leftMap i f g≫pullback.fst f g=pullback.fst (i≫f) g≫i:=by
  rw [leftMap,Category.assoc,←pullback.condition,←Category.assoc,
    pullbackRightPullbackFstIso_inv_fst]
@[reassoc] theorem leftMap_snd (i:U⟶X) (f:X⟶S) (g:Y⟶S) :
    leftMap i f g≫pullback.snd f g=pullback.snd (i≫f) g:=by
  simp only [leftMap,Category.assoc,pullbackRightPullbackFstIso_inv_snd_snd]

instance leftMap_open (i:U⟶X) (f:X⟶S) (g:Y⟶S) [IsOpenImmersion i] :
    IsOpenImmersion (leftMap i f g):=by unfold leftMap;infer_instance
instance leftMap_quasiCompact (i:U⟶X) (f:X⟶S) (g:Y⟶S) [QuasiCompact i] :
    QuasiCompact (leftMap i f g):=by unfold leftMap;infer_instance
instance leftMap_dense (i:U⟶X) (f:X⟶S) (g:Y⟶S)
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i] [Flat g] :
    IsSchemeTheoreticallyDominant (leftMap i f g):=by
  unfold leftMap
  infer_instance

/-- Change the right factor, retaining the specified relative product. -/
@[expose] def rightMap (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    pullback f (j≫g)⟶pullback f g:=
  (pullbackSymmetry f (j≫g)).hom≫leftMap j g f≫(pullbackSymmetry g f).hom
@[reassoc] theorem rightMap_fst (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    rightMap j f g≫pullback.fst f g=pullback.fst f (j≫g):=by
  simp [rightMap,Category.assoc,leftMap_snd]
@[reassoc] theorem rightMap_snd (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    rightMap j f g≫pullback.snd f g=pullback.snd f (j≫g)≫j:=by
  simp [rightMap,Category.assoc,leftMap_fst]

instance rightMap_open (j:V⟶Y) (f:X⟶S) (g:Y⟶S) [IsOpenImmersion j] :
    IsOpenImmersion (rightMap j f g):=by unfold rightMap;infer_instance
instance rightMap_quasiCompact (j:V⟶Y) (f:X⟶S) (g:Y⟶S) [QuasiCompact j] :
    QuasiCompact (rightMap j f g):=by unfold rightMap;infer_instance
instance rightMap_dense (j:V⟶Y) (f:X⟶S) (g:Y⟶S)
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [Flat f] :
    IsSchemeTheoreticallyDominant (rightMap j f g):=by
  unfold rightMap
  infer_instance

/-- Actual relative product of the two given chart maps. -/
@[expose] def productMap (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    pullback (i≫f) (j≫g)⟶pullback f g:=
  rightMap j (i≫f) g≫leftMap i f g
@[reassoc] theorem productMap_fst (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    productMap i j f g≫pullback.fst f g=pullback.fst (i≫f) (j≫g)≫i:=by
  simp [productMap,Category.assoc,leftMap_fst,rightMap_fst_assoc]
@[reassoc] theorem productMap_snd (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S) :
    productMap i j f g≫pullback.snd f g=pullback.snd (i≫f) (j≫g)≫j:=by
  simp [productMap,Category.assoc,leftMap_snd,rightMap_snd]
instance productMap_open (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    IsOpenImmersion (productMap i j f g):=by unfold productMap;infer_instance
instance productMap_quasiCompact (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S)
    [QuasiCompact i] [QuasiCompact j] :
    QuasiCompact (productMap i j f g):=by unfold productMap;infer_instance

/-- Products of quasi-compact schematically dense open charts remain
schematically dense when the factors are flat over the common base. -/
instance productMap_dense (i:U⟶X) (j:V⟶Y) (f:X⟶S) (g:Y⟶S)
    [IsOpenImmersion i] [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j] [Flat f] [Flat g] :
    IsSchemeTheoreticallyDominant (productMap i j f g):=by
  unfold productMap
  infer_instance
end SchematicProductDensity318
