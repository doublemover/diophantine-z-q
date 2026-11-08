module
public import BothExtractedComparison318
public import SpecAlgHomComposition318
public import BothInfinityCover318
public section
noncomputable section
namespace BothInfinityLocal318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]
abbrev LocalRing (A B:R) (i:Fin 3) := Localization.Away (BothInfinityCover318.chartElement A B i)
@[expose] def inputMap (A B:R) (i:Fin 3) : PairRing A B →ₐ[R] LocalRing A B i :=
  IsScalarTower.toAlgHom R (PairRing A B) (LocalRing A B i)
lemma left_unit (A B:R) : IsUnit (inputMap A B 0 (V1 A B)) := by
  have hh:=IsLocalization.Away.algebraMap_isUnit (S:=LocalRing A B 0)
    (BothInfinityCover318.chartElement A B 0)
  simpa only [inputMap,IsScalarTower.toAlgHom_apply,BothInfinityCover318.chartElement,
    Matrix.cons_val_zero] using hh
lemma right_unit (A B:R) : IsUnit (inputMap A B 1 (V2 A B)) := by
  have hh:=IsLocalization.Away.algebraMap_isUnit (S:=LocalRing A B 1)
    (BothInfinityCover318.chartElement A B 1)
  have he:BothInfinityCover318.chartElement A B (1:Fin 3)=V2 A B:=rfl
  simpa only [inputMap,IsScalarTower.toAlgHom_apply,he] using hh
@[expose] def localAddition (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i:Fin 3) :
    Spec (CommRingCat.of (LocalRing A B i)) ⟶ WeierstrassGluing318.scheme A B := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i) i
  · exact Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD
  · exact Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD
  · exact BothInfinityScheme318.addition A B
abbrev CommonRing (A B:R) (i j:Fin 3) := LocalRing A B i ⊗[PairRing A B] LocalRing A B j
@[expose] def left (A B:R) (i j:Fin 3) : LocalRing A B i →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R
@[expose] def right (A B:R) (i j:Fin 3) : LocalRing A B j →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R
lemma same_pair (A B:R) (i j:Fin 3) (a:PairRing A B) :
    left A B i j (inputMap A B i a)=right A B i j (inputMap A B j a) := by
  exact ((Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).commutes a).trans
    ((Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).commutes a).symm

lemma mixed_agreement {S:Type u} [CommRing S] [Algebra R S] (A B:R)
    (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:LocalRing A B 0 →ₐ[R] S) (g:LocalRing A B 1 →ₐ[R] S)
    (he:∀r, f (inputMap A B 0 r)=g (inputMap A B 1 r)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ localAddition A B hD 0=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ localAddition A B hD 1 := by
  have hfg:f.comp (inputMap A B 0)=g.comp (inputMap A B 1):=AlgHom.ext he
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)
  rw [←Category.assoc,(SpecAlgHomComposition318.map_comp (R:=R) (S:=InfinityInputAlgebra318.PairRing A B) (T:=LocalRing A B 0) (U:=S) f (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B))),←Category.assoc,(SpecAlgHomComposition318.map_comp (R:=R) (S:=InfinityInputAlgebra318.PairRing A B) (T:=LocalRing A B 1) (U:=S) g (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)))]
  simp only [BothInputSwap318.mixedLeft_natural,BothInputExtraction318.mixedPair_natural,hfg]
  exact (BothInputSwap318.mixed_agreement A B hD (g.comp (inputMap A B 1))
    (by rw [←hfg]; exact (left_unit A B).map f) ((right_unit A B).map g)).symm

lemma left_regular {S:Type u} [CommRing S] [Algebra R S] (A B:R)
    (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:LocalRing A B 0 →ₐ[R] S) (g:LocalRing A B 2 →ₐ[R] S)
    (he:∀r, f (inputMap A B 0 r)=g (inputMap A B 2 r)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ localAddition A B hD 0=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ localAddition A B hD 2 := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ BothInfinityScheme318.addition A B
  rw [←Category.assoc,(SpecAlgHomComposition318.map_comp (R:=R) (S:=InfinityInputAlgebra318.PairRing A B) (T:=LocalRing A B 0) (U:=S) f (BothInputSwap318.mixedLeft A B (inputMap A B 0) (left_unit A B)))]
  simp only [BothInputSwap318.mixedLeft_natural]
  exact (BothExtractedComparison318.reversed A B hD g (f.comp (inputMap A B 0))
    ((left_unit A B).map f) (fun r=>(he r).symm)).symm

lemma right_regular {S:Type u} [CommRing S] [Algebra R S] (A B:R)
    (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:LocalRing A B 1 →ₐ[R] S) (g:LocalRing A B 2 →ₐ[R] S)
    (he:∀r, f (inputMap A B 1 r)=g (inputMap A B 2 r)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ localAddition A B hD 1=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ localAddition A B hD 2 := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)).toRingHom) ≫
      MixedAdditionGluing318.coordinateAddition A B hD)=
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ BothInfinityScheme318.addition A B
  rw [←Category.assoc,(SpecAlgHomComposition318.map_comp (R:=R) (S:=InfinityInputAlgebra318.PairRing A B) (T:=LocalRing A B 1) (U:=S) f (BothInputExtraction318.mixedPair A B (inputMap A B 1) (right_unit A B)))]
  simp only [BothInputExtraction318.mixedPair_natural]
  exact (BothExtractedComparison318.direct A B hD g (f.comp (inputMap A B 1))
    ((right_unit A B).map f) (fun r=>(he r).symm)).symm

/-- All three actual local laws agree on their full tensor-product overlaps. -/
theorem local_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (i j:Fin 3) :
    Spec.map (CommRingCat.ofHom (left A B i j).toRingHom) ≫ localAddition A B hD i=
      Spec.map (CommRingCat.ofHom (right A B i j).toRingHom) ≫ localAddition A B hD j := by
  by_cases hij:i=j
  · subst j
    have he:left A B i i=right A B i i := by
      apply IsLocalization.algHom_ext (Submonoid.powers (BothInfinityCover318.chartElement A B i))
      apply AlgHom.ext
      exact same_pair A B i i
    rw [he]
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact mixed_agreement A B hD _ _ (same_pair A B 0 1)
  · exact left_regular A B hD _ _ (same_pair A B 0 2)
  · exact (mixed_agreement A B hD _ _ (fun r=>(same_pair A B 1 0 r).symm)).symm
  · exact right_regular A B hD _ _ (same_pair A B 1 2)
  · exact (left_regular A B hD _ _ (fun r=>(same_pair A B 2 0 r).symm)).symm
  · exact (right_regular A B hD _ _ (fun r=>(same_pair A B 2 1 r).symm)).symm
end BothInfinityLocal318
