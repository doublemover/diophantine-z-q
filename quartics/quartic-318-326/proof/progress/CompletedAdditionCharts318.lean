module
public import WeierstrassTwoChartCover318
public import WholeBothInfinity318
public import SymmetricMixedAddition318
public section
noncomputable section
namespace CompletedAdditionCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassTwoChartCover318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def chartStructure (A B:R) (i:Fin 2) : chart A B i ⟶ Spec (CommRingCat.of R) := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · exact ShortAffineScheme318.structureMap A B
  · exact InfinitySmooth318.structureMap A B
@[simp] theorem intoCurve_over_base (A B:R) (i:Fin 2) :
    intoCurve A B i ≫ WeierstrassGluing318.structureMap A B=chartStructure A B i := by
  fin_cases i
  · exact WeierstrassGluing318.finiteChart_structure A B
  · exact WeierstrassGluing318.infinityChart_structure A B
@[expose] def chartProductIso (A B:R) (i j:Fin 2) :
    (productCover A B).X ⟨i,j⟩ ≅ pullback (chartStructure A B i) (chartStructure A B j) :=
  pullback.congrHom (intoCurve_over_base A B i) (intoCurve_over_base A B j)

/-- The four already constructed whole input-chart additions. Compatibility on
the intersections is a separate statement, not assumed in this definition. -/
@[expose] def chartAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    pullback (chartStructure A B i) (chartStructure A B j) ⟶ WeierstrassGluing318.scheme A B := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun j=>Fin.elim0 j) j) j
    · exact FiniteAdditionGluing318.addition A B hD
    · exact SymmetricMixedAddition318.addition A B hD
  · refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun j=>Fin.elim0 j) j) j
    · exact MixedAdditionGluing318.addition A B hD
    · exact WholeBothInfinity318.addition A B hD
@[expose] def localAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    (productCover A B).X ⟨i,j⟩ ⟶ WeierstrassGluing318.scheme A B :=
  (chartProductIso A B i j).hom ≫ chartAddition A B hD i j
theorem chartAddition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    chartAddition A B hD i j ≫ WeierstrassGluing318.structureMap A B=
      pullback.fst (chartStructure A B i) (chartStructure A B j) ≫ chartStructure A B i := by
  fin_cases i <;> fin_cases j
  · exact FiniteAdditionGluing318.addition_over_base A B hD
  · exact SymmetricMixedAddition318.addition_over_base A B hD
  · exact MixedAdditionGluing318.addition_over_base A B hD
  · exact WholeBothInfinity318.addition_over_base A B hD
@[reassoc] theorem chartProductIso_fst (A B:R) (i j:Fin 2) :
    (chartProductIso A B i j).hom ≫ pullback.fst _ _=pullback.fst _ _ := by
  simp [chartProductIso,cover]
@[reassoc] theorem chartProductIso_snd (A B:R) (i j:Fin 2) :
    (chartProductIso A B i j).hom ≫ pullback.snd _ _=pullback.snd _ _ := by
  simp [chartProductIso,cover]
theorem localAddition_over_base (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 2) :
    localAddition A B hD i j ≫ WeierstrassGluing318.structureMap A B=
      (productCover A B).f ⟨i,j⟩ ≫ pullback.fst _ _ ≫ WeierstrassGluing318.structureMap A B := by
  rw [localAddition,Category.assoc,chartAddition_over_base,chartProductIso_fst_assoc]
  change pullback.fst _ _ ≫ chartStructure A B i=
    (GenericProductCover318.cover (cover A B) (cover A B) _ _).f ⟨i,j⟩ ≫ pullback.fst _ _ ≫ _
  rw [GenericProductCover318.fst_assoc]
  change pullback.fst _ _ ≫ chartStructure A B i=
    pullback.fst _ _ ≫ intoCurve A B i ≫ WeierstrassGluing318.structureMap A B
  rw [intoCurve_over_base]
end CompletedAdditionCharts318
