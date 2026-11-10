module
public import ContactRelativeWholeOpenSections318
public import ContactOriginalRelativeOverlapCoordinates318
public import OpenClutchedLocallyFree318
public import LineSheafTensorIsos318
public import OriginalClutchedFrameTransition318
public import OriginalOpenPullbackSectionScalar318
public section
noncomputable section
namespace ContactRelativeGeometricTwist318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
open ContactOriginalRelativeLineOverlap318 ContactRelativeWholeOpenSections318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- Actual Laurent R functions on the FULL original ambient overlap. -/
@[expose] def scalar : LaurentPolynomial R →+* Γ(curve R c,finiteOpen R c ⊓ infinityOpen R c) :=
  (((Scheme.ΓSpecIso (ring R c)).inv ≫ ((into R c).appIso ⊤).inv ≫
    (curve R c).presheaf.map (eqToHom (overlap_image R c).symm).op).hom).comp
      (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

@[expose] def monomialUnit (d : ℤ) : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T d
  inv := LaurentPolynomial.T (-d)
  val_inv := by rw [← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero]

@[expose] def transition (d : ℤ) : Γ(curve R c,finiteOpen R c ⊓ infinityOpen R c)ˣ :=
  Units.map (scalar R c).toMonoidHom (monomialUnit R d)

/-- Genuine geometric twist on the SAME arbitrary-R contact test. -/
@[expose] def line (d : ℤ) : Line (curve R c) where
  object := OpenClutchedLine318.line (finiteOpen R c) (infinityOpen R c) (transition R c d)
  Index := ULift Bool
  opens := OpenClutchedLocallyFree318.cover (finiteOpen R c) (infinityOpen R c)
  cover := OpenClutchedLocallyFree318.cover_top _ _ (cover R c)
  frame i := by
    rcases i with ⟨i⟩
    cases i
    · exact (OpenClutchedLine318.firstFrame _ _ (transition R c d)).symm
    · exact (OpenClutchedLine318.secondFrame _ _ (transition R c d)).symm

@[expose] def finiteFrame (d : ℤ) : (line R c d).object.restrict (finiteOpen R c).ι ≅
    SheafOfModules.unit (finiteOpen R c).toScheme.ringCatSheaf :=
  OpenClutchedLine318.firstFrame _ _ (transition R c d)
@[expose] def infinityFrame (d : ℤ) : (line R c d).object.restrict (infinityOpen R c).ι ≅
    SheafOfModules.unit (infinityOpen R c).toScheme.ringCatSheaf :=
  OpenClutchedLine318.secondFrame _ _ (transition R c d)
@[expose] def twist (L : Line (curve R c)) (d : ℤ) : Line (curve R c) :=
  LineSheafTensor318.line L (line R c d)

lemma frame_relation (d : ℤ) (s : Γ((line R c d).object,finiteOpen R c ⊓ infinityOpen R c)) :
    (OpenLineFrameCoordinates318.frame (line R c d).object (finiteOpen R c)
      (finiteFrame R c d).symm _ inf_le_left).symm s =
    (OpenLineFrameCoordinates318.frame (line R c d).object (infinityOpen R c)
      (infinityFrame R c d).symm _ inf_le_right).symm s * (transition R c d).val :=
  OriginalClutchedFrameTransition318.inverse_relation _ _ _ s

variable (L : Line (curve R c))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
@[expose] def ambientModule : Module (LaurentPolynomial R)
    Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) := Module.compHom _ (scalar R c)

lemma overlap_scalar (a : LaurentPolynomial R) (s : originalSections R c L) :
    overlapEquiv R c L (a • s) = scalar R c a • overlapEquiv R c L s := by
  have h := OriginalOpenPullbackSectionScalar318.scalar (into R c) L.object
    ((Scheme.ΓSpecIso (ring R c)).inv (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c a)) s
  change L.object.presheaf.map (eqToHom (overlap_image R c).symm).op
    (OriginalOpenPullbackSections318.sectionsEquiv (into R c) L.object
      (((Scheme.ΓSpecIso (ring R c)).inv (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c a)) • s)) = _
  rw [h,Scheme.Modules.map_smul]
  rfl

local instance : Module (LaurentPolynomial R) Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) :=
  ambientModule R c L
@[expose] def overlapLinear : originalSections R c L ≃ₗ[LaurentPolynomial R]
    Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) where
  __ := overlapEquiv R c L
  map_smul' := overlap_scalar R c L

lemma inverse_scalar (a : LaurentPolynomial R) (s : Γ(L.object,finiteOpen R c ⊓ infinityOpen R c)) :
    (overlapEquiv R c L).symm (scalar R c a • s) = a • (overlapEquiv R c L).symm s :=
  (overlapLinear R c L).symm.map_smul a s
end ContactRelativeGeometricTwist318
