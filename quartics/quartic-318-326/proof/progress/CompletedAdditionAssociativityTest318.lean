module
public import CompletedAdditionPoints318
public import CompletedAdditionTriple318
public section
noncomputable section
namespace CompletedAdditionAssociativityTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CompletedAdditionPoints318 CompletedAdditionTriple318
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
@[expose] def point1
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    (hb:t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫ WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=Spec.algebraMap (OpenJModel318.Base N) K) :
    CompletedAdditionPoints318.Points (K:=K) N :=
  ⟨t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N), (Category.assoc _ _ _).trans hb⟩
@[expose] def point2
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    (hb:t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫ WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=Spec.algebraMap (OpenJModel318.Base N) K) :
    CompletedAdditionPoints318.Points (K:=K) N :=
  ⟨t ≫ CompletedAdditionTriple318.second (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N), (Category.assoc _ _ _).trans ((congrArg (fun f=>t ≫ f) (CompletedAdditionTriple318.first_second_base (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).symm).trans hb)⟩
@[expose] def point3
    (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
    (hb:t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫ WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=Spec.algebraMap (OpenJModel318.Base N) K) :
    CompletedAdditionPoints318.Points (K:=K) N :=
  ⟨t ≫ CompletedAdditionTriple318.third (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N), (Category.assoc _ _ _).trans ((congrArg (fun f=>t ≫ f) (CompletedAdditionTriple318.first_third_base (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)).symm).trans hb)⟩
theorem pair12_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : pointPair N (point1 N t hb) (point2 N t hb)=t ≫ pair12 A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,pair12_fst]
    rfl
  · rw [pointPair_snd,Category.assoc,pair12_snd]
    rfl
theorem pair23_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : pointPair N (point2 N t hb) (point3 N t hb)=t ≫ pair23 A B := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,pair23_fst]
    rfl
  · rw [pointPair_snd,Category.assoc,pair23_snd]
    rfl
theorem sum12_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : (sumPoint N (point1 N t hb) (point2 N t hb)).val=
    t ≫ pair12 A B ≫ CompletedAddition318.addition A B hD := by
  change pointPair N (point1 N t hb) (point2 N t hb) ≫ _=_
  rw [pair12_point,Category.assoc]
theorem sum23_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : (sumPoint N (point2 N t hb) (point3 N t hb)).val=
    t ≫ pair23 A B ≫ CompletedAddition318.addition A B hD := by
  change pointPair N (point2 N t hb) (point3 N t hb) ≫ _=_
  rw [pair23_point,Category.assoc]
theorem leftPair_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : pointPair N (sumPoint N (point1 N t hb) (point2 N t hb)) (point3 N t hb)=
    t ≫ leftPair A B hD := by
  apply pullback.hom_ext
  · rw [pointPair_fst,sum12_value,Category.assoc,leftPair_fst]
  · rw [pointPair_snd,Category.assoc,leftPair_snd]
    rfl
theorem rightPair_point
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : pointPair N (point1 N t hb) (sumPoint N (point2 N t hb) (point3 N t hb))=
    t ≫ rightPair A B hD := by
  apply pullback.hom_ext
  · rw [pointPair_fst,Category.assoc,rightPair_fst]
    rfl
  · rw [pointPair_snd,sum23_value,Category.assoc,rightPair_snd]
theorem left_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : (sumPoint N (sumPoint N (point1 N t hb) (point2 N t hb)) (point3 N t hb)).val=
    t ≫ leftAssociate A B hD := by
  change pointPair N (sumPoint N (point1 N t hb) (point2 N t hb)) (point3 N t hb) ≫ _=_
  rw [leftPair_point,Category.assoc,leftAssociate]
theorem right_value
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : (sumPoint N (point1 N t hb) (sumPoint N (point2 N t hb) (point3 N t hb))).val=
    t ≫ rightAssociate A B hD := by
  change pointPair N (point1 N t hb) (sumPoint N (point2 N t hb) (point3 N t hb)) ≫ _=_
  rw [rightPair_point,Category.assoc,rightAssociate]
/-- Both actual associativity composites agree after every field-valued test
morphism over the original literal base. -/
theorem field_test
    (t:Spec (CommRingCat.of K) ⟶ triple A B)
    (hb:t ≫ first A B ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap (OpenJModel318.Base N) K) : t ≫ leftAssociate A B hD=t ≫ rightAssociate A B hD := by
  have hh:=congrArg Subtype.val (sumPoint_assoc N (point1 N t hb) (point2 N t hb) (point3 N t hb))
  rw [left_value,right_value] at hh
  exact hh
end CompletedAdditionAssociativityTest318
