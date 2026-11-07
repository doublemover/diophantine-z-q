module
public import FinitePairSchemeCover318
public import InfinityCrossMaps318
public import MixedCrossMaps318
public section
noncomputable section
namespace FiniteAdditionLocal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeChordAlgebra318 (PairRing)
open FinitePairCover318
open scoped TensorProduct
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R]

abbrev LocalRing (A B:R) (i:Fin 4) := Localization.Away (chartElement A B i)
@[expose] def localAddition (A B:R) (i:Fin 4) :
    Spec (CommRingCat.of (LocalRing A B i)) ⟶ WeierstrassGluing318.scheme A B := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact InfinityAdditionScheme318.addition A B false
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        exact InfinityAdditionScheme318.addition A B true

abbrev CommonRing (A B:R) (i j:Fin 4) := LocalRing A B i ⊗[PairRing A B] LocalRing A B j
@[expose] def left (A B:R) (i j:Fin 4) : LocalRing A B i →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R
@[expose] def right (A B:R) (i j:Fin 4) : LocalRing A B j →ₐ[R] CommonRing A B i j :=
  (Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).restrictScalars R

@[expose] def inputMap (A B:R) (i:Fin 4) : PairRing A B →ₐ[R] LocalRing A B i :=
  IsScalarTower.toAlgHom R (PairRing A B) (LocalRing A B i)

lemma same_pair (A B:R) (i j:Fin 4) (a:PairRing A B) :
    left A B i j (inputMap A B i a)=
      right A B i j (inputMap A B j a) := by
  exact ((Algebra.TensorProduct.includeLeft : LocalRing A B i →ₐ[PairRing A B] CommonRing A B i j).commutes a).trans
    ((Algebra.TensorProduct.includeRight : LocalRing A B j →ₐ[PairRing A B] CommonRing A B i j).commutes a).symm

lemma diagonal_maps (A B:R) (i:Fin 4) : left A B i i=right A B i i := by
  apply IsLocalization.algHom_ext (Submonoid.powers (chartElement A B i))
  apply AlgHom.ext
  exact same_pair A B i i

lemma local_over_base (A B:R) (i:Fin 4) : localAddition A B i ≫ WeierstrassGluing318.structureMap A B=
    Spec.map (CommRingCat.ofHom (algebraMap R (LocalRing A B i))) := by
  fin_cases i
  · change (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B) ≫ _=_
    rw [Category.assoc,WeierstrassGluing318.finiteChart_structure,RelativeChordScheme318.addition_over_base]
    rfl
  · change (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B) ≫ _=_
    rw [Category.assoc,WeierstrassGluing318.finiteChart_structure,TangentOpenScheme318.addition_over_base]
    rfl
  · exact InfinityAdditionScheme318.addition_over_base A B false
  · exact InfinityAdditionScheme318.addition_over_base A B true

section Agreements
variable {S:Type u} [CommRing S] [Algebra R S]
lemma same_chart_agreement (A B:R) (i:Fin 4) (φ ψ:LocalRing A B i →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (inputMap A B i a)=ψ (inputMap A B i a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ localAddition A B i=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ localAddition A B i := by
  have he : φ=ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (chartElement A B i))
    apply AlgHom.ext
    exact hp
  rw [he]

/-- Every pair of the four actual local addition maps agrees over every common algebra. -/
theorem local_agreement (A B:R) (i j:Fin 4) (φ:LocalRing A B i →ₐ[R] S)
    (ψ:LocalRing A B j →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (inputMap A B i a)=ψ (inputMap A B j a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ localAddition A B i=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ localAddition A B j := by
  by_cases hij:i=j
  · subst j; exact same_chart_agreement A B i φ ψ hp
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals dsimp only [localAddition]
  · change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    rw [←Category.assoc,FiniteCrossMaps318.scheme_agreement A B φ ψ hp,Category.assoc]
  · exact (MixedCrossMaps318.chord_infinity_chord_finite A B ψ φ (fun a=>(hp a).symm)).symm
  · exact (MixedCrossMaps318.tangent_infinity_chord_finite A B ψ φ (fun a=>(hp a).symm)).symm
  · change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)=
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    rw [←Category.assoc,←FiniteCrossMaps318.scheme_agreement A B ψ φ (fun a=>(hp a).symm),Category.assoc]
  · exact (MixedCrossMaps318.chord_infinity_tangent_finite A B ψ φ (fun a=>(hp a).symm)).symm
  · exact (MixedCrossMaps318.tangent_infinity_tangent_finite A B ψ φ (fun a=>(hp a).symm)).symm
  · exact MixedCrossMaps318.chord_infinity_chord_finite A B φ ψ hp
  · exact MixedCrossMaps318.chord_infinity_tangent_finite A B φ ψ hp
  · exact InfinityCrossMaps318.scheme_agreement A B φ ψ hp
  · exact MixedCrossMaps318.tangent_infinity_chord_finite A B φ ψ hp
  · exact MixedCrossMaps318.tangent_infinity_tangent_finite A B φ ψ hp
  · exact (InfinityCrossMaps318.scheme_agreement A B ψ φ (fun a=>(hp a).symm)).symm

end Agreements

end FiniteAdditionLocal318
