module
public import ContactOriginalWholeRestriction318
public import OriginalLineRationalCohomology318
public import ContactIntrinsicDifferentials318
public section
noncomputable section
namespace ContactOriginalCohomologyCoordinates318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
open ContactOriginalLaurentCoordinates318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Coordinates on the literal original ambient overlap sections. -/
def overlapCoordinates : Γ(L.object,finiteOpen c ⊓ infinityOpen c) ≃+
    LaurentVectorFiltration318.V ℚ (finiteRank c L) :=
  (overlapEquiv c L).symm.trans (coordinates c L).toAddEquiv

lemma finite_res (s : Γ(L.object,finiteOpen c)) :
    overlapCoordinates c L (L.object.presheaf.map
      (homOfLE inf_le_left : finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op s) =
    coordinates c L (finiteRestriction c L ((finiteSectionsEquiv c L).symm s)) := by
  have h := ContactOriginalWholeRestriction318.finite_square c L ((finiteSectionsEquiv c L).symm s)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h]
  simp only [overlapCoordinates,AddEquiv.trans_apply,AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply]

lemma infinity_res (s : Γ(L.object,infinityOpen c)) :
    overlapCoordinates c L (L.object.presheaf.map
      (homOfLE inf_le_right : finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op s) =
    coordinates c L (infinityRestriction c L ((infinitySectionsEquiv c L).symm s)) := by
  have h := ContactOriginalWholeRestriction318.infinity_square c L ((infinitySectionsEquiv c L).symm s)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h]
  simp only [overlapCoordinates,AddEquiv.trans_apply,AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply,LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply]

/-- This is the actual global line H1, carrying the Q action of the actual
ModuleScalar coefficient endomorphisms before any coordinate choice. -/
abbrev H1 := OriginalLineMayerVietorisQuotient318.H1 L
instance : Module ℚ (H1 c L) :=
  OriginalLineRationalCohomology318.cohomologyModule
    (ContactIntrinsicDifferentials318.structureMap c) L 1

/-- The actual original derived Mayer-Vietoris boundary, evaluated on
Laurent coordinates through the proved full-open comparison. -/
def coordinateBoundary : LaurentVectorFiltration318.V ℚ (finiteRank c L) →+ H1 c L :=
  (OriginalLineMayerVietorisQuotient318.boundary L (finiteOpen c) (infinityOpen c) (cover c)).comp
    (overlapCoordinates c L).symm.toAddMonoidHom

def boundaryLinear : LaurentVectorFiltration318.V ℚ (finiteRank c L) →ₗ[ℚ] H1 c L :=
  (coordinateBoundary c L).toRatLinearMap

lemma boundary_surjective : Function.Surjective (boundaryLinear c L) := by
  letI : IsIntegral (ContactProjectiveModel318.model c) :=
    ContactProjectiveModel318.model_integral c
  exact (OriginalLineMayerVietorisQuotient318.boundary_surjective L
    (finiteOpen c) (infinityOpen c) (finite_affine c) (infinity_affine c) (cover c)).comp
    (overlapCoordinates c L).symm.surjective

/-- The linearized map remains exactly the old derived boundary on every
original full-open section, not only on a chosen list of coefficients. -/
lemma boundary_original (s : Γ(L.object,finiteOpen c ⊓ infinityOpen c)) :
    boundaryLinear c L (overlapCoordinates c L s) =
      OriginalLineMayerVietorisQuotient318.boundary L
        (finiteOpen c) (infinityOpen c) (cover c) s := by
  change OriginalLineMayerVietorisQuotient318.boundary L _ _ _
    ((overlapCoordinates c L).symm ((overlapCoordinates c L) s)) = _
  rw [AddEquiv.symm_apply_apply]
end ContactOriginalCohomologyCoordinates318
