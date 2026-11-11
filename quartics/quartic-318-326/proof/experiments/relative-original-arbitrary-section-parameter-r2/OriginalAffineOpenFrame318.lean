module
public import OriginalOpenPullbackSectionScalar318
public import OriginalLineAffineModel318
public section
noncomputable section
namespace OriginalAffineOpenFrame318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (B : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec B ⟶ X) [IsOpenImmersion j]
  (L : Line X)
  (e : Γ(L.object,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(X,j ''ᵁ ⊤))

/-- Exact original affine-open scalar isomorphism, including the actual
open immersion's structure map and the Spec global-section counit. -/
@[expose] def ringEquivalence : Γ(X,j ''ᵁ ⊤) ≃+* B :=
  ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv

/-- Actual affine pulled line frame from a genuine ambient open frame.
The scalar action is B, not the ambient open's untransported section ring. -/
@[expose] def frame : OriginalLineAffineModel318.sections B (LineSheafPullback318.line j L) ≃ₗ[B] B where
  __ := (OriginalOpenPullbackSections318.sectionsEquiv j L.object).trans
    (e.toAddEquiv.trans (ringEquivalence B j).toAddEquiv)
  map_smul' b s := by
    change ringEquivalence B j (e (OriginalOpenPullbackSections318.sectionsEquiv j L.object
      ((Scheme.ΓSpecIso B).inv b • s))) =
      b * ringEquivalence B j (e (OriginalOpenPullbackSections318.sectionsEquiv j L.object s))
    rw [OriginalOpenPullbackSectionScalar318.scalar,map_smul]
    change ringEquivalence B j ((ringEquivalence B j).symm b *
      e (OriginalOpenPullbackSections318.sectionsEquiv j L.object s)) = _
    rw [map_mul,RingEquiv.apply_symm_apply]
end OriginalAffineOpenFrame318
