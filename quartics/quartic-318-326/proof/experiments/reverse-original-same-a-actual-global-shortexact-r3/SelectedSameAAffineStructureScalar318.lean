module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Read base scalars from the actual scheme map and sheaf restrictions

The map into a literal affine base determines the coefficient ring maps.
In a flat family the affine coordinate algebra is flat over that same base.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedSameAAffineStructureScalar318

universe u
variable {X : Scheme.{u}} {D : Type u} [CommRing D]

/-- The actual structure homomorphism to one ring of sections. -/
noncomputable def scalar (σ : X ⟶ Spec (CommRingCat.of D)) (U : X.Opens) :
    D →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of D)).inv ≫ σ.appLE ⊤ U (by simp)).hom

/-- This is the exact ambient restriction map, not a new algebra structure
chosen for the smaller affine. -/
theorem scalar_restriction (σ : X ⟶ Spec (CommRingCat.of D))
    {U W : X.Opens} (hWU : W ≤ U) :
    (X.presheaf.map (homOfLE hWU).op).hom.comp (scalar σ U) = scalar σ W := by
  unfold scalar
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

/-- The base module required by affine dual-number calculations is flat
for the literal sheaf-scalar ring map, not just after changing coefficients. -/
theorem scalar_flat (σ : X ⟶ Spec (CommRingCat.of D)) [Flat σ] {U : X.Opens}
    (hU : IsAffineOpen U) : (scalar σ U).Flat := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of D)).symm
  let a := σ.appLE ⊤ U (by simp)
  have hf : e.hom.hom.Flat :=
    RingHom.Flat.of_bijective e.commRingCatIsoToRingEquiv.bijective
  have hg : a.hom.Flat :=
    σ.flat_appLE (isAffineOpen_top _) hU _
  change (e.hom ≫ a).hom.Flat
  rw [CommRingCat.hom_comp]
  exact hf.comp hg

end SelectedSameAAffineStructureScalar318
