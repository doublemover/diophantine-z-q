module
public import LineFrameTopScalar318
public import GlobalScalarSheafEndomorphism318
public section
noncomputable section
namespace GlobalSectionFrameCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
  (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (r : Γ(U.toScheme,⊤))

/-- The exact coefficient in the ORIGINAL section ring, transported
from the open subscheme by its actual top-section isomorphism. -/
@[expose] def coefficient (W : X.Opens) (h : W ≤ U) : Γ(X,W) :=
  X.presheaf.map (homOfLE h).op ((LineFrameTopScalar318.ringTop U).hom r)

lemma section_natural {W Z : X.Opens} (h : W ≤ Z) :
    M.presheaf.map (homOfLE h).op (σ.app Z 1) = σ.app W 1 := by
  have hn := PresheafOfModules.naturality_apply σ.val (homOfLE h).op (1 : Γ(X,Z))
  simpa only [map_one] using hn.symm

variable (hσ : (Scheme.Modules.restrictUnitIso U.ι).inv ≫
    (Scheme.Modules.restrictFunctor U.ι).map σ =
      GlobalScalarSheafEndomorphism318.endomorphism U.toScheme r ≫ e.hom)
include hσ

/-- The normalized WHOLE module-sheaf identity gives the exact frame
coefficient on the original full open, including the actual site-over
comparison rather than a newly chosen section basis. -/
theorem top_coefficient :
    OpenLineFrameCoordinates318.frame M U e U le_rfl ((LineFrameTopScalar318.ringTop U).hom r) =
      σ.app U 1 := by
  let Z : X.Opens := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  have he : σ.app Z 1 = e.hom.app ⊤ r := by
    have hh := congrArg (fun f => f.app (⊤ : U.toScheme.Opens) (1 : Γ(U.toScheme,⊤))) hσ
    change σ.app Z ((U.ι.appIso ⊤).inv 1) =
      e.hom.app ⊤ ((GlobalScalarSheafEndomorphism318.endomorphism U.toScheme r).app ⊤ 1) at hh
    simpa only [map_one,GlobalScalarSheafEndomorphism318.endomorphism_value,
      homOfLE_refl,op_id,Functor.map_id,ConcreteCategory.id_apply] using hh
  have hf : OpenLineFrameCoordinates318.frame M U e Z
      (LineFrameTopScalar318.image_top U).le r = σ.app Z 1 :=
    (LineFrameTopScalar318.over_hom_app M U e ⊤ r).trans he.symm
  have ht := congrArg (fun s => M.presheaf.map
    (homOfLE (LineFrameTopScalar318.image_top U).symm.le).op s) hf
  rw [OpenLineFrameCoordinates318.natural,section_natural M σ] at ht
  exact ht

/-- Every smaller original open has the literal restriction of the same
regular coefficient. This is a full section equality, not a point test. -/
theorem coefficient_formula (W : X.Opens) (h : W ≤ U) :
    OpenLineFrameCoordinates318.frame M U e W h (coefficient U r W h) = σ.app W 1 := by
  have ht := congrArg (fun s => M.presheaf.map (homOfLE h).op s)
    (top_coefficient M U e σ r hσ)
  rw [OpenLineFrameCoordinates318.natural,section_natural M σ] at ht
  exact ht

/-- Inverse coordinate form for consumers that extract a cocycle from
the existing original line frames. -/
theorem inverse_coefficient (W : X.Opens) (h : W ≤ U) :
    (OpenLineFrameCoordinates318.frame M U e W h).symm (σ.app W 1) = coefficient U r W h := by
  rw [←coefficient_formula M U e σ r hσ W h,LinearEquiv.symm_apply_apply]
end GlobalSectionFrameCoordinates318
