module
public import NonreducedLineMayerVietoris318
public import ModuleScalar318
public section
noncomputable section
namespace OriginalCoefficientCohomology318
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite LineSheafClass318
open NonreducedLineRestriction318
variable (R : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R) (L : Line X)

/-- Actual coefficient functions from the original structure morphism,
on every ambient open of the original scheme. -/
@[expose] def scalar (U : X.Opens) : R →+* Γ(X,U) :=
  ((Scheme.ΓSpecIso R).inv ≫ p.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom

lemma scalar_restrict {U V : X.Opens} (j : U ⟶ V) (r : R) :
    X.presheaf.map j.op (scalar R p V r) = scalar R p U r := by
  change (((Scheme.ΓSpecIso R).inv ≫ p.appTop ≫ X.presheaf.map (homOfLE le_top).op ≫
    X.presheaf.map j.op) : R ⟶ Γ(X,U)) r = _
  rw [← Functor.map_comp]
  rfl

@[expose] def sectionModule (U : X.Opens) : Module R Γ(L.object,U) :=
  Module.compHom Γ(L.object,U) (scalar R p U)

/-- Original module-scalar endomorphisms, BEFORE any quotient or
cohomology identification. No action is transported from the Cech model. -/
def multiply (r : R) : additive L ⟶ additive L :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map (ModuleScalar318.map L.object (scalar R p ⊤ r))

lemma multiply_apply (r : R) (U : X.Opens) (s : Γ(L.object,U)) :
    (multiply R p L r).hom.app (op U) s = scalar R p U r • s := by
  change (ModuleScalar318.map L.object (scalar R p ⊤ r)).app U s = _
  rw [ModuleScalar318.map_apply,scalar_restrict]

lemma multiply_zero : multiply R p L 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply R p L 0).hom.app U s = 0
  rw [multiply_apply,map_zero,zero_smul]
lemma multiply_one : multiply R p L 1 = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change (multiply R p L 1).hom.app U s = s
  rw [multiply_apply,map_one,one_smul]
lemma multiply_add (r s : R) : multiply R p L (r+s) = multiply R p L r + multiply R p L s := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U t
  change (multiply R p L (r+s)).hom.app U t =
    (multiply R p L r).hom.app U t + (multiply R p L s).hom.app U t
  rw [multiply_apply,multiply_apply,multiply_apply,map_add,add_smul]
lemma multiply_mul (r s : R) : multiply R p L (r*s) = multiply R p L s ≫ multiply R p L r := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U t
  change (multiply R p L (r*s)).hom.app U t =
    (multiply R p L r).hom.app U ((multiply R p L s).hom.app U t)
  rw [multiply_apply,multiply_apply,multiply_apply,map_mul,mul_smul]

/-- Structural R action on the UNCHANGED actual derived Ext carrier,
induced directly by its actual coefficient endomorphisms. -/
@[expose] def cohomologyModule (n : ℕ) : Module R (Sheaf.H (additive L) n) where
  smul r x := Sheaf.H.map (multiply R p L r) n x
  one_smul x := by
    change Sheaf.H.map (multiply R p L 1) n x = x
    rw [multiply_one,Sheaf.H.map_id_apply]
  mul_smul r s x := by
    change Sheaf.H.map (multiply R p L (r*s)) n x =
      Sheaf.H.map (multiply R p L r) n (Sheaf.H.map (multiply R p L s) n x)
    rw [multiply_mul,Sheaf.H.map_comp_apply]
  smul_zero r := map_zero _
  smul_add r x y := map_add _ _ _
  add_smul r s x := by
    change Sheaf.H.map (multiply R p L (r+s)) n x =
      Sheaf.H.map (multiply R p L r) n x + Sheaf.H.map (multiply R p L s) n x
    rw [multiply_add,Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (multiply R p L 0) n x = 0
    rw [multiply_zero,Sheaf.H.map_apply,Ext.mk₀_zero,Ext.comp_zero]
end OriginalCoefficientCohomology318
