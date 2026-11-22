module

public import SelectedSameAAffineStructureScalar318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import SelectedSameAActualAffineSpecPushout318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all SelectedSameAAffineStructureScalar318

/-!
# The actual old affine chart gives both ring legs of the literal fibre

The two coefficient maps are read from the actual scheme structure.
No tensor algebra or affine pullback identification is supplied.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SelectedSameAOldFibreRingSquare318

universe u
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAAffineStructureScalar318

abbrev Sp (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

/-- The actual scheme structure on the affine is exactly its scalar map
obtained by reading the structure sheaf. -/
theorem affine_structure_from_scalar {Y : Scheme.{u}} {R : Type u} [CommRing R]
    (p : Y ⟶ Sp R) {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (scalar p U)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p
    (isAffineOpen_top (Sp R)) hU (show U ≤ p ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  change hU.fromSpec ≫ p =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U (by simp))
  exact h.symm

variable {k T : Type u} [CommRing k] [CommRing T]
variable {P A : Scheme.{u}} (p : P ⟶ Sp T) (i : A ⟶ P) (a : A ⟶ Sp k)
variable (x : T →+* k)

/-- Affine preimage of the actual original (unthickened) scheme fibre
inherits the same pullback from the ambient diagram. -/
theorem actual_old_affine_pullback [IsClosedImmersion i]
    (H : IsPullback i a p (Spec.map (CommRingCat.ofHom x)))
    {U : P.Opens} (hU : IsAffineOpen U) :
    IsPullback (Spec.map (i.app U))
      (Spec.map (CommRingCat.ofHom (scalar a (i ⁻¹ᵁ U))))
      (Spec.map (CommRingCat.ofHom (scalar p U)))
      (Spec.map (CommRingCat.ofHom x)) := by
  let hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have e : Spec.map (i.app U) ≫ hU.fromSpec = hV.fromSpec ≫ i := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec i hU hV le_rfl
  have hOpen : IsPullback (Spec.map (i.app U)) hV.fromSpec hU.fromSpec i :=
    IsOpenImmersion.isPullback _ _ _ _ e.symm (by
      rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])
  have h := hOpen.paste_vert H
  rw [affine_structure_from_scalar p hU,
    affine_structure_from_scalar a hV] at h
  exact h

/-- The scheme chart identity actually determines the four ordered
ring edges. This lemma does not ask for any of the algebra towers. -/
theorem actual_old_affine_ring_pushout [IsClosedImmersion i]
    (H : IsPullback i a p (Spec.map (CommRingCat.ofHom x)))
    {U : P.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom x) (CommRingCat.ofHom (scalar p U))
      (CommRingCat.ofHom (scalar a (i ⁻¹ᵁ U))) (i.app U) := by
  have h : IsPullback (i.app U).op
      (CommRingCat.ofHom (scalar a (i ⁻¹ᵁ U))).op
      (CommRingCat.ofHom (scalar p U)).op (CommRingCat.ofHom x).op :=
    IsPullback.of_map_of_faithful (F := Scheme.Spec)
      (actual_old_affine_pullback p i a x H hU)
  exact h.unop

/-- On that same actual old chart, the literal ring p-map is smooth. -/
theorem actual_smooth_scalar [Smooth p] {U : P.Opens} (hU : IsAffineOpen U) :
    (scalar p U).Smooth := by
  have h : Smooth (hU.fromSpec ≫ p) := inferInstance
  have h' : Smooth (Spec.map (CommRingCat.ofHom (scalar p U))) :=
    affine_structure_from_scalar p hU ▸ h
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h'

end SelectedSameAOldFibreRingSquare318
