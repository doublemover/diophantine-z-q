module
public import AffineProductEvaluation318
public import CompletedAdditionCharts318
public section
noncomputable section
namespace ChartAliasTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318
open AlgebraChartEvaluation318 AffineProductEvaluation318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
example (A B:R)
 (x:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B 0) (chartStructure A B 0))
 (h:x ≫ pullback.fst _ _ ≫ chartStructure A B 0 = Spec.algebraMap R S) :
 x ≫ pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫ Spec.algebraMap R (F A B) = Spec.algebraMap R S := by
 change x ≫ pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫ Spec.algebraMap R (F A B) = Spec.algebraMap R S at h
 exact h
end ChartAliasTest318
