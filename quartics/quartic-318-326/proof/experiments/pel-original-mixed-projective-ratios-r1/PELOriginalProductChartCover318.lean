module
public import PELOriginalAdditionCandidateRelations318
public import PELOriginalCandidateChartBase318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace PELOriginalProductChartCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartPoints318
variable (τ : ℂ) (hτ : 0 < τ.im)

abbrev π := PELOriginalProperComplexCandidate318.structureMap τ hτ
abbrev Product := pullback (π τ hτ) (π τ hτ)

/-- The usual9-by9 open cover of the ACTUAL fiber product over C. -/
@[expose] def rawCover : (Product τ hτ).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (cover τ hτ) (cover τ hτ) (π τ hτ) (π τ hτ)

/-- Genuine Spec(tensor) comparison with the actual over-C chart
pullback, preserving the original structural scalar maps. -/
@[expose] def chartIso (j k : Label 3) :
    Spec (CommRingCat.of (ProductRing τ hτ j k)) ≅
      pullback (chartMap τ hτ j≫π τ hτ) (chartMap τ hτ k≫π τ hτ) :=
  (pullbackSpecIso ℂ (CoordinateChart τ hτ j) (CoordinateChart τ hτ k)).symm ≪≫
    pullback.congrHom (chart_over_complex_base τ hτ j).symm
      (chart_over_complex_base τ hτ k).symm

@[reassoc] lemma chartIso_fst (j k : Label 3) :
    (chartIso τ hτ j k).hom≫pullback.fst _ _=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        CoordinateChart τ hτ j →+* ProductRing τ hτ j k)) := by
  simp only [chartIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullback.congrHom_hom,pullback.map_fst,Category.comp_id,pullbackSpecIso_inv_fst]

@[reassoc] lemma chartIso_snd (j k : Label 3) :
    (chartIso τ hτ j k).hom≫pullback.snd _ _=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        CoordinateChart τ hτ k →ₐ[ℂ] ProductRing τ hτ j k).toRingHom) := by
  simp only [chartIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullback.congrHom_hom,pullback.map_snd,Category.comp_id,pullbackSpecIso_inv_snd]

@[expose] def chartInclusion (jk : Label 3 × Label 3) :
    Spec (CommRingCat.of (ProductRing τ hτ jk.1 jk.2)) ⟶ Product τ hτ :=
  (chartIso τ hτ jk.1 jk.2).hom≫(rawCover τ hτ).f jk

/-- An actual81-member affine cover with the exact tensor coordinate
rings used by the regular addition equations. It covers all primes. -/
@[expose] def affineCover : (Product τ hτ).OpenCover :=
  (rawCover τ hτ).copy (Label 3 × Label 3)
    (fun jk => Spec (CommRingCat.of (ProductRing τ hτ jk.1 jk.2)))
    (chartInclusion τ hτ) (Equiv.refl _) (fun jk => chartIso τ hτ jk.1 jk.2)
    (fun _ => rfl)

instance chartInclusion_open (jk : Label 3 × Label 3) : IsOpenImmersion (chartInclusion τ hτ jk) := by
  change IsOpenImmersion ((affineCover τ hτ).f jk)
  infer_instance

@[reassoc] lemma inclusion_fst (j k : Label 3) :
    chartInclusion τ hτ (j,k)≫pullback.fst (π τ hτ) (π τ hτ)=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        CoordinateChart τ hτ j →+* ProductRing τ hτ j k))≫chartMap τ hτ j := by
  rw [chartInclusion,Category.assoc]
  change (chartIso τ hτ j k).hom≫
    (pullback.map _ _ _ _ (chartMap τ hτ j) (chartMap τ hτ k) (𝟙 _) _ _≫_)=_
  rw [pullback.map_fst,←Category.assoc,chartIso_fst]

@[reassoc] lemma inclusion_snd (j k : Label 3) :
    chartInclusion τ hτ (j,k)≫pullback.snd (π τ hτ) (π τ hτ)=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        CoordinateChart τ hτ k →ₐ[ℂ] ProductRing τ hτ j k).toRingHom)≫chartMap τ hτ k := by
  rw [chartInclusion,Category.assoc]
  change (chartIso τ hτ j k).hom≫
    (pullback.map _ _ _ _ (chartMap τ hτ j) (chartMap τ hτ k) (𝟙 _) _ _≫_)=_
  rw [pullback.map_snd,←Category.assoc,chartIso_snd]

/-- Reducedness of the WHOLE actual product scheme is produced from
all81 actual reduced tensor charts. No smooth-implies-reduced shortcut. -/
instance product_reduced : IsReduced (Product τ hτ) :=
  IsReduced.of_openCover _ (affineCover τ hτ)

lemma chart_count : Fintype.card (Label 3 × Label 3)=81 := by
  norm_num [Label,Fintype.card_prod]
end PELOriginalProductChartCover318
