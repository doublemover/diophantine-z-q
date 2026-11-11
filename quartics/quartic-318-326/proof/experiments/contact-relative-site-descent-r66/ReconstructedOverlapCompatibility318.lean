module
public import CanonicalGeometricOverlap318
public section
noncomputable section
namespace ReconstructedOverlapCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : OriginalLineOverlapCoaction318.first R S L ⟶ OriginalLineOverlapCoaction318.second R S L)
  (hdiag : OriginalGeometricDiagonal318.Diagonal R S L τ)
  (htriple : OriginalGeometricTriple318.Cocycle R S L τ)

abbrev descendedModule := AffineCoalgebraModule318.descended (algebraMap R S)
  (AffineCoalgebraLine318.faithfullyFlat R S)
  (OriginalGeometricAffineLine318.coalgebra R S L τ hdiag htriple)
abbrev comparison := OriginalGeometricAffineLine318.pullbackIso R S L τ hdiag htriple

lemma comparison_eq : comparison R S L τ hdiag htriple =
    CanonicalTildeOverlap318.coverComparison (CanonicalTildeOverlap318.ringMap R S)
      (descendedModule R S L τ hdiag htriple) L
      (OriginalGeometricAffineLine318.moduleIso R S L τ hdiag htriple) := by
  apply Iso.ext
  change (AffineCoalgebraLine318.pullbackIso R S
    (OriginalGeometricAffineLine318.coalgebra R S L τ hdiag htriple) L (Iso.refl _)).hom = _
  rw [AffineCoalgebraLine318.pullbackIso_hom]
  simp only [AffineCoalgebraLine318.scalarIso, CanonicalTildeOverlap318.coverComparison,
    Iso.trans_hom, Iso.refl_hom, Category.comp_id, Iso.app_hom,
    Functor.mapIso_hom, OriginalLineAffineModel318.canonicalIso_hom]
  rfl

/-- The displayed reconstruction pullback isomorphism carries the actual
canonical geometric overlap of the reconstructed base line to the original
input overlap. This is exact sheaf compatibility, not only coaction recovery. -/
lemma original_overlap :
    (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map
        (comparison R S L τ hdiag htriple).inv ≫
      CanonicalTildeOverlap318.sheafOverlap R S (descendedModule R S L τ hdiag htriple) ≫
      (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map
        (comparison R S L τ hdiag htriple).hom = τ := by
  rw [comparison_eq]
  change CanonicalGeometricOverlap318.overlap R S (descendedModule R S L τ hdiag htriple) L
    (OriginalGeometricAffineLine318.moduleIso R S L τ hdiag htriple) = τ
  apply (OriginalLineOverlapCoaction318.homEquiv R S L).injective
  rw [CanonicalGeometricOverlap318.coaction]
  exact OriginalGeometricAffineLine318.coaction_recovered R S L τ hdiag htriple

/-- Equivalent commuting-square form with the unchanged original input
sheaf overlap on the right. -/
lemma comparison_commutes :
    CanonicalTildeOverlap318.sheafOverlap R S (descendedModule R S L τ hdiag htriple) ≫
      (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map
        (comparison R S L τ hdiag htriple).hom =
    (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map
      (comparison R S L τ hdiag htriple).hom ≫ τ := by
  have h := congrArg
    (fun k => (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map
      (comparison R S L τ hdiag htriple).hom ≫ k)
    (original_overlap R S L τ hdiag htriple)
  let P := Scheme.Modules.pullback (Spec.map (leftMap R S S))
  let e := comparison R S L τ hdiag htriple
  have hc : P.map e.hom ≫ P.map e.inv=𝟙 _ := by
    calc
      _ = P.map (e.hom ≫ e.inv) := (P.map_comp _ _).symm
      _ = P.map (𝟙 _) := congrArg (fun k => P.map k) e.hom_inv_id
      _ = 𝟙 _ := P.map_id _
  have ht := congrArg (fun k => k ≫
    CanonicalTildeOverlap318.sheafOverlap R S (descendedModule R S L τ hdiag htriple) ≫
      (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map e.hom) hc.symm
  have hh : P.map e.hom ≫ P.map e.inv ≫
      CanonicalTildeOverlap318.sheafOverlap R S (descendedModule R S L τ hdiag htriple) ≫
        (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map e.hom=P.map e.hom ≫ τ := h
  exact (by simpa only [Category.assoc,Category.id_comp] using ht).trans hh
end ReconstructedOverlapCompatibility318
