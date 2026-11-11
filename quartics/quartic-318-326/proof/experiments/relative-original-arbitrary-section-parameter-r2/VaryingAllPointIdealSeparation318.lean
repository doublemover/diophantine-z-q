module
public import VaryingPointChartFreeness318
public import VaryingFreePointIdealSeparation318
public section
noncomputable section
namespace VaryingAllPointIdealSeparation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- ALL actual parameter points are determined by their whole original
quotient ideal, without any global free-basis assumption. Local freeness
is proved only after the full pulled-back parameter cover is refined by
actual affine opens. -/
lemma ideal_injective : Function.Injective (VaryingParameterPointIdeal318.ideal R A ι S) := by
  intro x y h
  apply Subtype.ext
  let U := (VaryingWordChartGluing318.cover R A ι).pullback₁ x.val
  apply Scheme.Cover.hom_ext U _ _
  intro w
  let V := (U.X w).affineOpenCover
  apply Scheme.Cover.hom_ext V.openCover _ _
  intro i
  let T := V.X i
  let f₀ : Spec T ⟶ Spec (CommRingCat.of S) := V.f i ≫ U.f w
  let ψ : S →+* T := (Spec.preimage f₀).hom
  letI : Algebra R T := (ψ.comp (algebraMap R S)).toAlgebra
  let f : S →ₐ[R] T := { __ := ψ, commutes' := fun _ => rfl }
  have hf : VaryingSourceCoefficientPullback318.coefficientChange R S T f=f₀ := Spec.map_preimage f₀
  let g := V.f i ≫ pullback.snd x.val (VaryingWordChartGluing318.into R A ι w)
  have hg : (VaryingParameterPoint318.map R A ι S T f x).val=
      g ≫ VaryingWordChartGluing318.into R A ι w := by
    change VaryingSourceCoefficientPullback318.coefficientChange R S T f ≫ x.val=_
    rw [hf]
    change (V.f i ≫ pullback.fst x.val (VaryingWordChartGluing318.into R A ι w)) ≫ _=
      (V.f i ≫ pullback.snd x.val (VaryingWordChartGluing318.into R A ι w)) ≫ _
    rw [Category.assoc,Category.assoc,pullback.condition]
  have hi : VaryingParameterPointIdeal318.ideal R A ι T (VaryingParameterPoint318.map R A ι S T f x)=
      VaryingParameterPointIdeal318.ideal R A ι T (VaryingParameterPoint318.map R A ι S T f y) := by
    rw [VaryingPointIdealNaturality318.ideal_map,VaryingPointIdealNaturality318.ideal_map,h]
  have he := VaryingFreePointIdealSeparation318.eq_of_ideal R A ι T
    (VaryingPointChartFreeness318.free R A ι T (VaryingParameterPoint318.map R A ι S T f x) w g hg) hi
  have hm := congrArg Subtype.val he
  change VaryingSourceCoefficientPullback318.coefficientChange R S T f ≫ x.val=
    VaryingSourceCoefficientPullback318.coefficientChange R S T f ≫ y.val at hm
  rw [hf] at hm
  simpa only [f₀,Category.assoc] using hm
end VaryingAllPointIdealSeparation318
