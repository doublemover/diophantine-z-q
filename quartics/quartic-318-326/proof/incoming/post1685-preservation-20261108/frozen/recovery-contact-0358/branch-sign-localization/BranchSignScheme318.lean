module
public import BranchSignLocalization318
public section
noncomputable section
namespace BranchSignScheme318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318 BranchSignLocalization318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
@[expose] def map (i:Fin 4) (b:Fin 4→Bool):
    Spec (CommRingCat.of (B c i))⟶Spec (CommRingCat.of (B c i)):=
  Spec.map (CommRingCat.ofHom (sign c i b).toRingHom)
lemma source_square (i:Fin 4) (b:Fin 4→Bool):
    map c i b≫Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder c) (B c i)))=
      Spec.map (CommRingCat.ofHom (algebraMap (SourceOrder c) (B c i)))≫SourceSignChart318.map c b:=by
  unfold map SourceSignChart318.map
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (on_source c i b)
/-- Exact restriction of every original whole-source sign to the entire
actual finite branch chart, including its ramified locus. -/
@[reassoc] theorem actual_square (i:Fin 4) (b:Fin 4→Bool):
    map c i b≫ContactIntrinsicFrames318.branchEmbedding c i=
      ContactIntrinsicFrames318.branchEmbedding c i≫ContactGlobalSigns318.map c b:=by
  unfold ContactIntrinsicFrames318.branchEmbedding
  rw [←Category.assoc,source_square,Category.assoc,SourceSignChart318.actual_square,Category.assoc]
theorem flip_square (i:Fin 4):
    Spec.map (CommRingCat.ofHom (flip c i).toRingHom)≫ContactIntrinsicFrames318.branchEmbedding c i=
      ContactIntrinsicFrames318.branchEmbedding c i≫ContactGlobalSigns318.map c (SourceCharacterFields318.flip i):=
  actual_square c i (SourceCharacterFields318.flip i)
end BranchSignScheme318
