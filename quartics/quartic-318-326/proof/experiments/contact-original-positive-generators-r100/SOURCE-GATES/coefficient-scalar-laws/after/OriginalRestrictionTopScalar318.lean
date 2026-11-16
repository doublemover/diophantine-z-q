module
public import LineFrameTopScalar318
public import ModuleScalar318
public section
noncomputable section
namespace OriginalRestrictionTopScalar318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- Literal original module sections on the FULL open, recovered from the
canonical open subscheme by its actual image equality. -/
def moduleTop : Γ(M.restrict U.ι,⊤) ≃+ Γ(M,U) :=
  (M.presheaf.mapIso (eqToIso (LineFrameTopScalar318.image_top U).symm).op).addCommGroupIsoToAddEquiv

lemma scalar (a : Γ(U.toScheme,⊤)) (s : Γ(M.restrict U.ι,⊤)) :
    moduleTop M U (a • s) = (LineFrameTopScalar318.ringTop U).hom a • moduleTop M U s := by
  change M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op (a • s) =
    X.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op a •
      M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op s
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ a s
  have ht := congrArg
    (fun t : Γ(M,U.ι ''ᵁ ⊤) =>
      M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op t) h
  rw [Scheme.Modules.map_smul] at ht
  simp only [Scheme.Modules.restrictAppIso,Scheme.Opens.ι_appIso,
    Iso.refl_hom,Iso.refl_inv] at ht
  change M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op (a • s) =
    X.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op a •
      M.presheaf.map (eqToHom (LineFrameTopScalar318.image_top U).symm).op s at ht
  exact ht

/-- The original ModuleScalar action on the open subscheme corresponds to
exactly the original ambient coefficient action, with no transported guess. -/
lemma multiply (a : Γ(U.toScheme,⊤)) (s : Γ(M.restrict U.ι,⊤)) :
    moduleTop M U ((ModuleScalar318.map (M.restrict U.ι) a).app ⊤ s) =
      (LineFrameTopScalar318.ringTop U).hom a • moduleTop M U s := by
  rw [ModuleScalar318.map_apply]
  change moduleTop M U ((U.toScheme.presheaf.map (𝟙 (op ⊤)) a) • s) = _
  have hi : U.toScheme.presheaf.map (𝟙 (op ⊤)) a = a :=
    congrArg (fun g : Γ(U.toScheme,⊤) ⟶ Γ(U.toScheme,⊤) => g a)
      (U.toScheme.presheaf.map_id (op ⊤))
  rw [hi]
  exact scalar M U a s
end OriginalRestrictionTopScalar318
