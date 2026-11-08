module
public import FourRootSignBaseChange318
public import ContactOverlapAlgebraMaps318
public import SourceSignFieldComparison318
public import FifthCharacterSource318
public section
noncomputable section
namespace ContactRootReciprocals318
open Polynomial ContactKummerOrder318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=InfinityFieldCoordinates318.L c
local instance rawField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
@[expose] def root (i:Fin 4):SourceOrder c:=FourRootOrderSigns318.generator (coefficient c) i
@[expose] def openRoot (i:Fin 4):OpenOrder c:=SourceOpenFractionField318.orderToOpen c (root c i)
@[expose] def fullRoot : SourceOrder c:=∏i:Fin 4,root c i

theorem embedding_root (i:Fin 4):embedding c (root c i)=InfinityFieldCoordinates318.root c i:=
  FourRootSignBaseChange318.coefficientMap_generator (coefficient c) K i

theorem embedding_fullRoot:embedding c (fullRoot c)=
    CharacterRoot318.root (SourceKummerField318.parameter c) Finset.univ:=by
  simp only [fullRoot,map_prod,embedding_root,CharacterRoot318.root,InfinityFieldCoordinates318.root]

theorem open_embedding_root (i:Fin 4):SourceOpenFractionField318.openEmbedding c (openRoot c i)=
    InfinityFieldCoordinates318.root c i:=by
  rw [openRoot,SourceOpenFractionField318.openEmbedding_on_order,embedding_root]

theorem root_square (i:Fin 4):root c i^2=algebraMap ℚ[X] (SourceOrder c) (coefficient c i):=
  FourRootOrderSigns318.generator_square (coefficient c) i

lemma other_index (i j:Fin 4) (hij:i≠j):∃k:Fin 3,FourRootPivot318.indices j k.succ=i:=by
  fin_cases i <;> fin_cases j <;> simp_all [FourRootPivot318.indices] <;> decide

/-- Every root other than the branch pivot is a genuine unit on its entire
branch chart. This is the denominator needed for a regular fifth form. -/
theorem branch_root_unit (i j:Fin 4) (hij:i≠j):IsUnit
    (algebraMap (SourceOrder c) (ContactIntrinsicFrames318.BranchRing c j) (root c i)):=by
  obtain ⟨k,hk⟩:=other_index i j hij
  have hd:algebraMap ℚ[X] (SourceOrder c) (coefficient c i)∣SourceDenominatorCover318.denominator c j:=by
    apply _root_.map_dvd (algebraMap ℚ[X] (SourceOrder c))
    rw [←hk]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  have hu:=IsLocalization.Away.isUnit_of_dvd (S:=ContactIntrinsicFrames318.BranchRing c j)
    (SourceDenominatorCover318.denominator c j) hd
  rw [←root_square,map_pow] at hu
  exact (isUnit_pow_iff (by decide:(2:ℕ)≠0)).mp hu

/-- The reciprocal root at infinity is the regular function u/c0 on the
entire infinity chart, with its actual whole-overlap restriction. -/
theorem infinity_reciprocal_relation:
    ContactOverlapAlgebraMaps318.infinityMap c
      (algebraMap ℚ (InfinityGlobalChart318.InfinityOrder c) (↑(c 0)⁻¹:ℚ)*
        ContactFrameNormalization318.infinityCoordinate c)*openRoot c 0=1:=by
  apply SourceOpenFractionField318.openEmbedding_injective c
  rw [map_mul,map_one,map_mul,AlgHom.commutes,ContactOverlapAlgebraMaps318.infinityMap_coordinate,
    map_mul,RingHom.map_rat_algebraMap,SourceInfinityOverlap318.u_embedding,open_embedding_root]
  rw [InfinityFieldCoordinates318.u,InfinityFieldCoordinates318.constant]
  have hr:InfinityFieldCoordinates318.root c 0≠0:=InfinityFieldCoordinates318.root_ne_zero c 0
  field_simp
  rw [←map_mul,Units.inv_mul,map_one]

/-- The full product is exactly the frozen fifth-character source element,
not another square root with an unspecified sign. -/
theorem actual_fifth_root:
    fullRoot SourceTwistArithmetic318.units=FifthCharacterSource318.toSource
      (AdjoinRoot.root (QuadraticPresentation318.polynomial FifthCharacterPolynomial318.quartic)):=by
  apply embedding_injective SourceTwistArithmetic318.units
  rw [embedding_fullRoot,FifthCharacterSource318.source_root_embedding]
  rfl
end ContactRootReciprocals318
