module

public import SelectedSameADualNumberFibreKernel318
public import SelectedSameAAffineStructureScalar318
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all SelectedSameAAffineStructureScalar318

/-!
# The reduction on the original affine chosen in the actual family

Start from its true global special-fibre square. Restrict to a given affine
using the inverse-image open. This supplies the marked local pullback and
the exact quotient kernel, not an independently chosen affine reduction.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SelectedSameAActualAffineFibre318

open SelectedSameADualNumberFibreKernel318 SelectedSameAAffineStructureScalar318

universe u
variable {K : Type u} [CommRing K]
variable {X R : Scheme.{u}} (σ : X ⟶ S (D K)) (ι : R ⟶ X) (r : R ⟶ S K)

/-- The actual scheme structure on the affine is exactly its scalar map
obtained by reading the structure sheaf. -/
theorem affine_structure_from_scalar {A : Type u} [CommRing A]
    (p : X ⟶ S A) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = sp (scalar p U) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p
    (isAffineOpen_top (S A)) hU (show U ≤ p ⁻¹ᵁ ⊤ by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  change hU.fromSpec ≫ p =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U (by simp))
  exact h.symm

/-- The chosen affine square is genuinely the restriction of the same
global fibre square. The top map is produced by the original sheaf pullback. -/
theorem affine_fibre_isPullback [IsClosedImmersion ι]
    (H : IsPullback ι r σ (sp (projection K)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsPullback (Spec.map (ι.app U)) ((hU.preimage ι).fromSpec ≫ r)
      (sp (scalar σ U)) (sp (projection K)) := by
  let hR : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
  have e : Spec.map (ι.app U) ≫ hU.fromSpec = hR.fromSpec ≫ ι := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec ι hU hR le_rfl
  have hOpen : IsPullback (Spec.map (ι.app U)) hR.fromSpec hU.fromSpec ι :=
    IsOpenImmersion.isPullback _ _ _ _ e.symm (by
      rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])
  have h := hOpen.paste_vert H
  rw [affine_structure_from_scalar σ hU] at h
  exact h

/-- Surjectivity and the precise image-of-epsilon kernel for this actual
original reduction map, under the global closed-fibre identification. -/
theorem actual_chart_reduction [IsClosedImmersion ι]
    (H : IsPullback ι r σ (sp (projection K)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (ι.app U).hom ∧
      RingHom.ker (ι.app U).hom =
        Ideal.span ({scalar σ U (ε K)} : Set Γ(X, U)) := by
  letI : Algebra (D K) Γ(X, U) := (scalar σ U).toAlgebra
  have h := affine_fibre_isPullback σ ι r H hU
  exact actualAffineFibre_ker K Γ(X, U) Γ(R, ι ⁻¹ᵁ U) (ι.app U).hom h.isoPullback
    h.isoPullback_hom_fst

end SelectedSameAActualAffineFibre318
