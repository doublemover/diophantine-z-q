module
public import CompletedAdditionPoints318
public import CompletedAdditionTriple318
public section
noncomputable section
namespace PointAliasTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {K:Type} [Field K] [Algebra (OpenJModel318.Base N) K]
#check CompletedAdditionPoints318.Points
#check CompletedAdditionPoints318.pointPair
@[expose] def firstPoint
 (t:Spec (CommRingCat.of K) ⟶ CompletedAdditionTriple318.triple (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))
 (hb:t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
    WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)=Spec.algebraMap (OpenJModel318.Base N) K) :
 CompletedAdditionPoints318.Points (K:=K) N :=
 ⟨t ≫ CompletedAdditionTriple318.first (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N),
    (Category.assoc _ _ _).trans hb⟩
#check firstPoint
end PointAliasTest318
