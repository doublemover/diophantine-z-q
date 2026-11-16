module
public import OriginalOpenPullbackSectionScalar318
public import ContactOriginalWholeTwistScalar318
public import ContactOriginalCohomologyCoordinates318
public section
noncomputable section
namespace ContactOriginalOverlapLaurentScalar318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLaurentOverlap318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalCohomologyCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))
abbrev A := OriginalLaurentProjectiveOverlap318.Ring

/-- The coefficient action on the original ambient overlap is induced by
the ACTUAL original Laurent projection/ring comparison, before coordinates. -/
def ambientModule : Module A Γ(L.object,finiteOpen c ⊓ infinityOpen c) :=
  Module.compHom Γ(L.object,finiteOpen c ⊓ infinityOpen c) (ContactOriginalTwistingLine318.scalar c)

/-- Exact scalar normalization of the old whole-overlap additive comparison.
This is not uniqueness of an arbitrarily transported A-module structure. -/
lemma overlap_scalar (a : A) (s : ContactCommonLaurentModule318.common c L) :
    overlapEquiv c L (a • s) =
      ContactOriginalTwistingLine318.scalar c a • overlapEquiv c L s := by
  have h := OriginalOpenPullbackSectionScalar318.scalar (into c) L.object
    ((projection c).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) s
  change L.object.presheaf.map (eqToHom (overlap_image c).symm).op
      (OriginalOpenPullbackSections318.sectionsEquiv (into c) L.object
        (((projection c).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) • s)) = _
  rw [h,Scheme.Modules.map_smul]
  rfl

local instance : Module A Γ(L.object,finiteOpen c ⊓ infinityOpen c) := ambientModule c L

/-- The same old additive comparison is linear for the independently
defined original Laurent scalar action. -/
def overlapLinear : ContactCommonLaurentModule318.common c L ≃ₗ[A]
    Γ(L.object,finiteOpen c ⊓ infinityOpen c) where
  __ := overlapEquiv c L
  map_smul' := overlap_scalar c L

/-- Original ambient scalar multiplication has its literal Laurent
coordinate value under the previously constructed common-module coordinates. -/
lemma coordinates_scalar (a : A) (s : Γ(L.object,finiteOpen c ⊓ infinityOpen c)) :
    overlapCoordinates c L (ContactOriginalTwistingLine318.scalar c a • s) =
      a • overlapCoordinates c L s := by
  change ContactOriginalRestrictionCoordinates318.coordinates c L
    ((overlapLinear c L).symm (a • s)) =
      a • ContactOriginalRestrictionCoordinates318.coordinates c L ((overlapLinear c L).symm s)
  rw [LinearEquiv.map_smul,LinearEquiv.map_smul]

lemma coordinates_monomial (d : ℤ) (s : Γ(L.object,finiteOpen c ⊓ infinityOpen c)) :
    overlapCoordinates c L (ContactOriginalTwistingLine318.scalar c (LaurentPolynomial.T d) • s) =
      (LaurentPolynomial.T d : A) • overlapCoordinates c L s := coordinates_scalar c L _ s
end ContactOriginalOverlapLaurentScalar318
