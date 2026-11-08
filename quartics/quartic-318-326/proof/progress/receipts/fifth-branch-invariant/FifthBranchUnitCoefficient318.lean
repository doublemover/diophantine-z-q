module
public import BranchOriginalCoordinate318
public import FifthGlobalPullbackNormalization318
public section
noncomputable section
namespace FifthBranchUnitCoefficient318
open SourceTwistArithmetic318 ContactKummerOrder318 ContactRootReciprocals318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev B (j:Fin 4):=ContactIntrinsicFrames318.BranchRing units j
abbrev O:=OpenOrder units
abbrev L:=ContactRootReciprocals318.L units
local instance originalField:Field L:=(KummerTensorField318.source_raw_field units).toField
@[expose] def branchRoot (j i:Fin 4):B j:=algebraMap (SourceOrder units) (B j) (root units i)
@[expose] def otherRoots (j:Fin 4):B j:=∏i∈Finset.univ.erase j,branchRoot j i
lemma otherRoots_unit (j:Fin 4):IsUnit (otherRoots j):=by
  apply IsUnit.prod_iff.mpr
  intro i hi
  exact branch_root_unit units i j (Finset.mem_erase.mp hi).1
@[expose] def inverseOthers (j:Fin 4):B j:=↑((otherRoots_unit j).unit⁻¹)
lemma inverse_relation (j:Fin 4):otherRoots j*inverseOthers j=1:=by
  rw [←(otherRoots_unit j).unit_spec]
  exact Units.mul_inv _
/-- Exact coefficient of the actual fifth quotient invariant in dy_j. -/
@[expose] def coefficient (j:Fin 4):B j:=
  algebraMap ℚ (B j) ((-82320:ℚ)/(units j:ℚ))*inverseOthers j
lemma coefficient_unit (j:Fin 4):IsUnit (coefficient j):=by
  apply IsUnit.mul
  · exact (IsUnit.mk0 _ (div_ne_zero (by norm_num) (units j).ne_zero)).map (algebraMap ℚ (B j))
  · exact Units.isUnit _
@[expose] def raw (j:Fin 4):B j→+*L:=
  (SourceOpenFractionField318.openEmbedding units).comp (ContactOverlapAlgebraMaps318.branchMap units j).toRingHom
lemma raw_root (j i:Fin 4):raw j (branchRoot j i)=InfinityFieldCoordinates318.root units i:=by
  change SourceOpenFractionField318.openEmbedding units
    (BranchOverlapLocalization318.toOpen units j (algebraMap (SourceOrder units) (B j) (root units i)))=_
  rw [BranchOverlapLocalization318.toOpen_on_source,SourceOpenFractionField318.openEmbedding_on_order,embedding_root]
lemma raw_coordinate (j:Fin 4):raw j (ContactFrameNormalization318.sourceCoordinate units j)=
    InfinityFieldCoordinates318.root units j:=by
  rw [BranchOriginalCoordinate318.coordinate_eq_root]
  exact raw_root j j
lemma raw_otherRoots (j:Fin 4):raw j (otherRoots j)=ComplementCharacterIndependence318.root units j:=by
  simp only [otherRoots,map_prod,raw_root]
  rfl
lemma raw_inverse (j:Fin 4):raw j (inverseOthers j)=(ComplementCharacterIndependence318.root units j)⁻¹:=by
  have hh:=congrArg (raw j) (inverse_relation j)
  rw [map_mul,map_one,raw_otherRoots] at hh
  exact eq_inv_of_mul_eq_one_right hh
lemma raw_coefficient (j:Fin 4):raw j (coefficient j)=
    algebraMap ℚ L ((-82320:ℚ)/(units j:ℚ))*(ComplementCharacterIndependence318.root units j)⁻¹:=by
  rw [coefficient,map_mul,RingHom.map_rat_algebraMap,raw_inverse]
lemma scale_identity (j:Fin 4):(-82320:ℚ)/(units j:ℚ)=
    FifthInvariantScalar318.scale*(2*(↑((units j)⁻¹):ℚ)):=by
  simp only [FifthInvariantScalar318.scale,Units.val_inv_eq_inv_val,div_eq_mul_inv]
  ring
end FifthBranchUnitCoefficient318
