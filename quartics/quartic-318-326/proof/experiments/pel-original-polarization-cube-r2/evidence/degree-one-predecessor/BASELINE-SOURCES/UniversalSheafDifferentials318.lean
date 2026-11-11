module
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace UniversalSheafDifferentials318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} {S : X.Opensᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ X.presheaf)

/-- The actual presheaf of universal relative differentials on every open. -/
@[expose] def presheaf : X.PresheafOfModules := relativeDifferentials' φ

/-- The intrinsic differential sheaf: actual O-module sheafification of universal
relative differentials, defined on the entire scheme rather than a chosen chart. -/
@[expose] def omega : X.Modules :=
  (PresheafOfModules.sheafification (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj (presheaf φ)

/-- The universal presheaf derivation gives a genuine Hom/derivation equivalence. -/
@[expose] def presheafEquiv (M : X.PresheafOfModules) :
    (presheaf φ ⟶ M) ≃ PresheafOfModulesOfCommRing.Derivation' M φ where
  toFun f := (derivation' φ).postcomp f
  invFun d := (isUniversal' φ).desc d
  left_inv _f := (isUniversal' φ).postcomp_injective _ _ ((isUniversal' φ).fac _)
  right_inv d := (isUniversal' φ).fac d

/-- The genuine sheafification adjunction, with its identity scalar restriction. -/
@[expose] def sheafificationEquiv (M : X.Modules) :
    (omega φ ⟶ M) ≃ (presheaf φ ⟶ M.val) :=
  PresheafOfModules.sheafificationHomEquiv (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

/-- Universality against every actual sheaf of modules, not only quasi-coherent
ones, free ones, global coefficient records, or a selected finite cover. -/
@[expose] def universalEquiv (M : X.Modules) :
    (omega φ ⟶ M) ≃ PresheafOfModulesOfCommRing.Derivation' M.val φ :=
  (sheafificationEquiv φ M).trans (presheafEquiv φ M.val)

/-- The actual global universal derivation into the intrinsic differential sheaf. -/
@[expose] def D : PresheafOfModulesOfCommRing.Derivation' (omega φ).val φ := universalEquiv φ (omega φ) (𝟙 _)

theorem postcomp_comp {M N P : X.PresheafOfModules} (d : PresheafOfModulesOfCommRing.Derivation' M φ)
    (f : M ⟶ N) (g : N ⟶ P) : (d.postcomp f).postcomp g=d.postcomp (f ≫ g) := by
  ext U a
  rfl

/-- The representability equivalence is literally composition with the actual
global universal derivation. -/
theorem universalEquiv_apply (M : X.Modules) (f : omega φ ⟶ M) :
    universalEquiv φ M f=(D φ).postcomp f.val := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R:=X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right (𝟙 (omega φ)) f
  change sheafificationEquiv φ (omega φ) (𝟙 _) ≫ f.val = sheafificationEquiv φ M (𝟙 _ ≫ f) at h
  rw [Category.id_comp] at h
  change (derivation' φ).postcomp (sheafificationEquiv φ M f)=
    ((derivation' φ).postcomp (sheafificationEquiv φ (omega φ) (𝟙 _))).postcomp f.val
  rw [postcomp_comp, h]

/-- Descend an actual sheaf-valued derivation through its intrinsic universal
object. No local factorization or compatibility assumption is supplied. -/
@[expose] def desc {M : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) : omega φ ⟶ M :=
  (universalEquiv φ M).symm d

theorem desc_fac {M : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) :
    (D φ).postcomp (desc φ d).val=d := by
  rw [←universalEquiv_apply]
  exact (universalEquiv φ M).apply_symm_apply d

theorem hom_ext {M : X.Modules} (f g : omega φ ⟶ M)
    (h : (D φ).postcomp f.val=(D φ).postcomp g.val) : f=g := by
  apply (universalEquiv φ M).injective
  simpa only [universalEquiv_apply] using h

/-- The full existence-and-uniqueness universal property as an ordinary theorem. -/
theorem existsUnique_desc {M : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) :
    ∃! f : omega φ ⟶ M, (D φ).postcomp f.val=d := by
  refine ⟨desc φ d,desc_fac φ d,?_⟩
  intro f hf
  exact hom_ext φ f _ (hf.trans (desc_fac φ d).symm)
end UniversalSheafDifferentials318
