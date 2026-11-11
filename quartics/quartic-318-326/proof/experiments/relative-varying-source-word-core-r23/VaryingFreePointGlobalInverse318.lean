module
public import VaryingFreePointAffineTests318
public section
noncomputable section
namespace VaryingFreePointGlobalInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingFreeParameterPoints318.FreePoint R A ι S)
/-- The genuine right inverse on the intrinsic global-free locus. The
whole pullback of the parameter chart cover is refined by actual affine
covers; on each affine test the existing chart inverse applies. -/
lemma classify_recover : VaryingFreeParameterPoints318.classify R A ι S
    (VaryingFreeParameterPoints318.recover R A ι S x)=x := by
  apply Subtype.ext
  apply Subtype.ext
  let U := (VaryingWordChartGluing318.cover R A ι).pullback₁ x.val.val
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
  have hf : VaryingSourceCoefficientPullback318.coefficientChange R S T f=f₀ :=
    Spec.map_preimage f₀
  let g : Spec T ⟶ VaryingNormalizedOverlapScheme318.chart R A ι w :=
    V.f i ≫ pullback.snd x.val.val (VaryingWordChartGluing318.into R A ι w)
  have hc : VaryingSourceCoefficientPullback318.coefficientChange R S T f ≫ x.val.val=
      g ≫ VaryingWordChartGluing318.into R A ι w := by
    rw [hf]
    change (V.f i ≫ pullback.fst x.val.val (VaryingWordChartGluing318.into R A ι w)) ≫ _=
      (V.f i ≫ pullback.snd x.val.val (VaryingWordChartGluing318.into R A ι w)) ≫ _
    rw [Category.assoc,Category.assoc,pullback.condition]
  have ht := VaryingFreePointAffineTests318.test_identity R A ι S x T f w g hc
  rw [hf] at ht
  simpa only [f₀,Category.assoc] using ht
end VaryingFreePointGlobalInverse318
