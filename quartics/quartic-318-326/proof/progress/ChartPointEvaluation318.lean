module
public import AffineProductEvaluation318
public import AlgebraChartCompatibility318
public import CompletedAdditionCharts318
import all Init.Data.Fin.Lemmas
public section
noncomputable section
namespace ChartPointEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318 CompletedAdditionCharts318
open AlgebraChartCompatibility318 AffineProductEvaluation318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma chartStructure_zero (A B:R) : chartStructure A B 0=ShortAffineScheme318.structureMap A B := rfl
lemma chartStructure_one (A B:R) : chartStructure A B 1=InfinitySmooth318.structureMap A B := rfl
@[expose] def input (A B:R) (i:Fin 2) (x:Spec (CommRingCat.of S) ⟶ chart A B i)
    (h:x ≫ chartStructure A B i=Spec.algebraMap R S) : Input (S:=S) A B := by
  revert x h
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · intro x h
    exact .inl (toAlgHom x h)
  · intro x h
    exact .inr (toAlgHom x h)
theorem image_input (A B:R) (i:Fin 2) (x:Spec (CommRingCat.of S) ⟶ chart A B i)
    (h:x ≫ chartStructure A B i=Spec.algebraMap R S) :
    image A B (input A B i x h)=x ≫ intoCurve A B i := by
  fin_cases i
  · exact congrArg (fun f=>f ≫ WeierstrassGluing318.finiteChart A B) (map_toAlgHom x h)
  · exact congrArg (fun f=>f ≫ WeierstrassGluing318.infinityChart A B) (map_toAlgHom x h)

theorem evaluation (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2)
    (x:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B i) (chartStructure A B j))
    (h1:x ≫ pullback.fst _ _ ≫ chartStructure A B i=Spec.algebraMap R S)
    (h2:x ≫ pullback.snd _ _ ≫ chartStructure A B j=Spec.algebraMap R S) :
    x ≫ chartAddition A B hD i j=
      evaluate A B hD (input A B i (x ≫ pullback.fst _ _) (by simpa only [Category.assoc] using h1))
        (input A B j (x ≫ pullback.snd _ _) (by simpa only [Category.assoc] using h2)) := by
  revert x h1 h2
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun j=>Fin.elim0 j) j) j
    · intro x h1 h2
      change x ≫ pullback.fst (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.F A B) = Spec.algebraMap R S at h1
      change x ≫ pullback.snd (ShortAffineScheme318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.F A B) = Spec.algebraMap R S at h2
      exact finite_evaluation A B hD x _ _
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h1)).symm
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h2)).symm
    · intro x h1 h2
      change x ≫ pullback.fst (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.F A B) = Spec.algebraMap R S at h1
      change x ≫ pullback.snd (ShortAffineScheme318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.I A B) = Spec.algebraMap R S at h2
      exact symmetric_evaluation A B hD x _ _
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h1)).symm
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h2)).symm
  · refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun j=>Fin.elim0 j) j) j
    · intro x h1 h2
      change x ≫ pullback.fst (InfinitySmooth318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.I A B) = Spec.algebraMap R S at h1
      change x ≫ pullback.snd (InfinitySmooth318.structureMap A B) (ShortAffineScheme318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.F A B) = Spec.algebraMap R S at h2
      exact mixed_evaluation A B hD x _ _
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h1)).symm
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h2)).symm
    · intro x h1 h2
      change x ≫ pullback.fst (InfinitySmooth318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.I A B) = Spec.algebraMap R S at h1
      change x ≫ pullback.snd (InfinitySmooth318.structureMap A B) (InfinitySmooth318.structureMap A B) ≫
        Spec.algebraMap R (AlgebraChartEvaluation318.I A B) = Spec.algebraMap R S at h2
      exact both_evaluation A B hD x _ _
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h1)).symm
        (map_toAlgHom (R:=R) _ (by simpa only [Category.assoc] using h2)).symm

theorem agreement_over_algebra (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j k l:Fin 2)
    (x:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B i) (chartStructure A B j))
    (y:Spec (CommRingCat.of S) ⟶ pullback (chartStructure A B k) (chartStructure A B l))
    (hx1:x ≫ pullback.fst _ _ ≫ chartStructure A B i=Spec.algebraMap R S)
    (hx2:x ≫ pullback.snd _ _ ≫ chartStructure A B j=Spec.algebraMap R S)
    (hy1:y ≫ pullback.fst _ _ ≫ chartStructure A B k=Spec.algebraMap R S)
    (hy2:y ≫ pullback.snd _ _ ≫ chartStructure A B l=Spec.algebraMap R S)
    (h1:x ≫ pullback.fst _ _ ≫ intoCurve A B i=y ≫ pullback.fst _ _ ≫ intoCurve A B k)
    (h2:x ≫ pullback.snd _ _ ≫ intoCurve A B j=y ≫ pullback.snd _ _ ≫ intoCurve A B l) :
    x ≫ chartAddition A B hD i j=y ≫ chartAddition A B hD k l := by
  rw [evaluation A B hD i j x hx1 hx2,evaluation A B hD k l y hy1 hy2]
  apply evaluate_congr
  · simpa only [image_input,Category.assoc] using h1
  · simpa only [image_input,Category.assoc] using h2
end ChartPointEvaluation318
