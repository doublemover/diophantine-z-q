module
public import AffineSplitDiagonalTranspose318
public import AffineCocycleLine318
public section
noncomputable section
namespace OriginalGeometricAffineLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : OriginalLineOverlapCoaction318.first R S L ⟶
    OriginalLineOverlapCoaction318.second R S L)
  (hdiag : OriginalGeometricDiagonal318.Diagonal R S L τ)
  (htriple : OriginalGeometricTriple318.Cocycle R S L τ)

/-- Effective rank-one line reconstruction from the genuine geometric
module-sheaf overlap equations on the affine Cech tensor spectra. The input
is an original sheaf morphism, not an assumed module coalgebra. -/
@[expose] def line : Line (Spec R) :=
  AffineCocycleLine318.line R S L (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ)
    (AffineSplitDiagonalTranspose318.diagonal_to_module R S L τ hdiag)
    (OriginalGeometricTriple318.cocycle_to_module R S L τ htriple)

/-- The reconstructed line pulls back to the unchanged covering line. -/
@[expose] def pullbackIso :
    (LineSheafPullback318.line (Spec.map (AffineCoalgebraLine318.ringMap R S))
      (line R S L τ hdiag htriple)).object ≅ L.object :=
  AffineCocycleLine318.pullbackIso R S L (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ)
    (AffineSplitDiagonalTranspose318.diagonal_to_module R S L τ hdiag)
    (OriginalGeometricTriple318.cocycle_to_module R S L τ htriple)

/-- The actual original coalgebra, with both laws derived geometrically. -/
abbrev coalgebra := AffineOverlapCoassociativity318.coalgebra R S
  (OriginalLineAffineModel318.sections S L) (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ)
  (AffineSplitDiagonalTranspose318.diagonal_to_module R S L τ hdiag)
  (OriginalGeometricTriple318.cocycle_to_module R S L τ htriple)

abbrev moduleIso := AffineCoalgebraModule318.moduleIso (algebraMap R S)
  (AffineCoalgebraLine318.faithfullyFlat R S) (coalgebra R S L τ hdiag htriple)

/-- Transport of the reconstructed canonical coaction through the original
module comparison, with its source exactly the original section module. -/
@[expose] def reconstructedCoaction : OriginalLineAffineModel318.sections S L ⟶
    AffineOverlapCoaction318.comonadObject R S (OriginalLineAffineModel318.sections S L) :=
  (moduleIso R S L τ hdiag htriple).inv ≫
    (ModuleCat.extendScalars (algebraMap R S)).map
      ((AffineCoalgebraModule318.adjunction (algebraMap R S)).unit.app
        (AffineCoalgebraModule318.descended (algebraMap R S) (AffineCoalgebraLine318.faithfullyFlat R S)
          (coalgebra R S L τ hdiag htriple))) ≫
    (AffineCoalgebraModule318.adjunction (algebraMap R S)).toComonad.toFunctor.map
      (moduleIso R S L τ hdiag htriple).hom

lemma coaction_recovered : reconstructedCoaction R S L τ hdiag htriple =
    OriginalLineOverlapCoaction318.homEquiv R S L τ := by
  have h := AffineCocycleLine318.original_coaction_compatibility R S L
    (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ)
    (AffineSplitDiagonalTranspose318.diagonal_to_module R S L τ hdiag)
    (OriginalGeometricTriple318.cocycle_to_module R S L τ htriple)
  change _ = (moduleIso R S L τ hdiag htriple).hom ≫
    OriginalLineOverlapCoaction318.homEquiv R S L τ at h
  unfold reconstructedCoaction
  rw [h, Iso.inv_hom_id_assoc]

/-- Recover the actual original overlap sheaf morphism, not just its class,
under the established original geometric/coaction correspondence. -/
lemma overlap_recovered :
    (OriginalLineOverlapCoaction318.homEquiv R S L).symm
      (reconstructedCoaction R S L τ hdiag htriple) = τ := by
  rw [coaction_recovered, Equiv.symm_apply_apply]
end OriginalGeometricAffineLine318
