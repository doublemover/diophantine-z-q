module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace GlobalScalarSheafEndomorphism318
open AlgebraicGeometry CategoryTheory
variable (X : Scheme)

/-- The compatible family of restrictions of a genuine global regular
function, as a section of the actual structure module sheaf. -/
@[expose] def section (r : Γ(X,⊤)) : (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun U => X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
    (by
      intro U V f
      change X.presheaf.map f
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) = _
      rw [←ConcreteCategory.comp_apply,←Functor.map_comp]
      rfl)

@[expose] def endomorphism (r : Γ(X,⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (section X r)

lemma endomorphism_one : endomorphism X 1 = 𝟙 _ := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  rw [endomorphism,Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change X.presheaf.map _ 1 = 1
  exact map_one _

lemma endomorphism_value (r : Γ(X,⊤)) (U : X.Opens) :
    (endomorphism X r).app U 1 =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r := by
  have h := congrArg (fun s => s.val (.op U))
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.apply_symm_apply (section X r))
  exact h

lemma endomorphism_apply (r : Γ(X,⊤)) (U : X.Opens) (a : Γ(X,U)) :
    (endomorphism X r).app U a =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a := by
  have he := Scheme.Modules.Hom.app_smul (endomorphism X r) a (1 : Γ(X,U))
  simpa only [smul_eq_mul,mul_one,endomorphism_value,mul_comm] using he

@[reassoc] lemma endomorphism_comp (r s : Γ(X,⊤)) :
    endomorphism X r ≫ endomorphism X s = endomorphism X (r*s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  simp only [Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,endomorphism_apply,map_mul]
  ring

/-- A genuine regular unit acts by an actual module-sheaf isomorphism. -/
@[expose] def unitIso (u : Γ(X,⊤)ˣ) :
    SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf where
  hom := endomorphism X u.val
  inv := endomorphism X (↑u⁻¹)
  hom_inv_id := by rw [endomorphism_comp,Units.val_inv,endomorphism_one]
  inv_hom_id := by rw [endomorphism_comp,Units.inv_val,endomorphism_one]
end GlobalScalarSheafEndomorphism318
