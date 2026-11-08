module
public import ContactRootReciprocals318
public import ContactCharacterFrameValues318
public section
noncomputable section
namespace FifthFormLocalCoefficients318
open SourceTwistArithmetic318 ContactKummerOrder318 ContactRootReciprocals318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev B (j:Fin 4):=ContactIntrinsicFrames318.BranchRing units j
abbrev I:=InfinityGlobalChart318.InfinityOrder units
abbrev O:=OpenOrder units
abbrev L:=ContactRootReciprocals318.L units
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero : CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
@[expose] def chosen (j:Fin 4):Fin 4:=if j=0 then 1 else 0
lemma chosen_ne (j:Fin 4):chosen j≠j:=by
  unfold chosen
  split_ifs with h
  · subst j;decide
  · exact Ne.symm h
@[expose] def branchInverse (j:Fin 4):B j:=
  ↑((branch_root_unit units (chosen j) j (chosen_ne j)).unit⁻¹)
@[expose] def branchCoefficient (j:Fin 4):B j:=
  algebraMap ℚ (B j) (2/(CharacterPublishedModels318.scaleUnit (chosen j):ℚ))*branchInverse j
@[expose] def infinityReciprocal:I:=algebraMap ℚ I (↑(units 0)⁻¹:ℚ)*
  ContactFrameNormalization318.infinityCoordinate units
@[expose] def infinityCoefficient:I:=
  algebraMap ℚ I (2/(CharacterPublishedModels318.scaleUnit 0:ℚ))*infinityReciprocal

lemma branch_inverse_relation (j:Fin 4):
    algebraMap (SourceOrder units) (B j) (root units (chosen j))*branchInverse j=1:=by
  rw [←(branch_root_unit units (chosen j) j (chosen_ne j)).unit_spec]
  exact Units.mul_inv _

lemma branch_inverse_image (j:Fin 4):SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.branchMap units j (branchInverse j))=
      (InfinityFieldCoordinates318.root units (chosen j))⁻¹:=by
  have h:=congrArg (fun b:B j=>SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.branchMap units j b)) (branch_inverse_relation j)
  simp only [map_mul,map_one] at h
  have hr:SourceOpenFractionField318.openEmbedding units
      (ContactOverlapAlgebraMaps318.branchMap units j
        (algebraMap (SourceOrder units) (B j) (root units (chosen j))))=
      InfinityFieldCoordinates318.root units (chosen j):=by
    rw [show ContactOverlapAlgebraMaps318.branchMap units j
      (algebraMap (SourceOrder units) (B j) (root units (chosen j)))=
        SourceOpenFractionField318.orderToOpen units (root units (chosen j)) from
          BranchOverlapLocalization318.toOpen_on_source units j _,
      SourceOpenFractionField318.openEmbedding_on_order,embedding_root]
  rw [hr] at h
  exact eq_inv_of_mul_eq_one_right h

lemma infinity_inverse_image:SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.infinityMap units infinityReciprocal)=
      (InfinityFieldCoordinates318.root units 0)⁻¹:=by
  have h:=congrArg (SourceOpenFractionField318.openEmbedding units)
    (infinity_reciprocal_relation units)
  rw [map_mul,map_one,open_embedding_root] at h
  exact eq_inv_of_mul_eq_one_left h

lemma branch_coefficient_image (j:Fin 4):SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.branchMap units j (branchCoefficient j))=
      algebraMap ℚ L (2/(CharacterPublishedModels318.scaleUnit (chosen j):ℚ))*
        (InfinityFieldCoordinates318.root units (chosen j))⁻¹:=by
  rw [branchCoefficient,map_mul,AlgHom.commutes,map_mul,RingHom.map_rat_algebraMap,branch_inverse_image]
lemma infinity_coefficient_image:SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.infinityMap units infinityCoefficient)=
      algebraMap ℚ L (2/(CharacterPublishedModels318.scaleUnit 0:ℚ))*
        (InfinityFieldCoordinates318.root units 0)⁻¹:=by
  rw [infinityCoefficient,map_mul,AlgHom.commutes,map_mul,RingHom.map_rat_algebraMap,infinity_inverse_image]

lemma root_times_complement (i:Fin 4):InfinityFieldCoordinates318.root units i*
    ComplementCharacterIndependence318.root units i=FifthCharacterField318.root:=by
  change FourRootAutomorphisms318.generator (SourceKummerField318.parameter units) i*
    (∏j∈Finset.univ.erase i,FourRootAutomorphisms318.generator (SourceKummerField318.parameter units) j)=
      ∏j:Fin 4,FourRootAutomorphisms318.generator (SourceKummerField318.parameter units) j
  exact Finset.mul_prod_erase _ _ (Finset.mem_univ i)

lemma normalized_product (s:ℚˣ) (a b:L):
    (algebraMap ℚ L (2/(s:ℚ))*a⁻¹)*(algebraMap ℚ L ((s:ℚ)/2)*b⁻¹)=(a*b)⁻¹:=by
  have hs:(2/(s:ℚ))*((s:ℚ)/2)=1:=by field_simp
  calc
    _ = algebraMap ℚ L ((2/(s:ℚ))*((s:ℚ)/2))*(a*b)⁻¹:=by rw [map_mul,mul_inv_rev];ring
    _ = _ :=by rw [hs,map_one,one_mul]

/-- All local formulas have exactly dt/fullRoot as coefficient in the
original field. This is only coefficient comparison; global gluing is separate. -/
lemma common_coefficient (i:Fin 4):
    (algebraMap ℚ L (2/(CharacterPublishedModels318.scaleUnit i:ℚ))*
      (InfinityFieldCoordinates318.root units i)⁻¹)*
        ContactCharacterFrameValues318.rawValue (ContactCharacterAffinePullback318.finiteForm i)=
      FifthCharacterField318.root⁻¹:=by
  rw [ContactCharacterFrameValues318.raw_formula,normalized_product,root_times_complement]
end FifthFormLocalCoefficients318
