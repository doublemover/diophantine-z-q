module
public import OriginalCoefficientCohomology318
public section
noncomputable section
namespace OriginalCoefficientUnitIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R) (L : Line X)

/-- The original coefficient function acts on the actual module sheaf,
not only on an H0 presentation or on its underlying additive sheaf. -/
@[expose] def multiply (r : R) : L.object ⟶ L.object :=
  ModuleScalar318.map L.object (OriginalCoefficientCohomology318.scalar R p ⊤ r)
lemma apply (r : R) (V : X.Opens) (s : Γ(L.object,V)) :
    (multiply R p L r).app V s=OriginalCoefficientCohomology318.scalar R p V r • s := by
  rw [multiply,ModuleScalar318.map_apply,OriginalCoefficientCohomology318.scalar_restrict]
lemma one : multiply R p L 1=𝟙 L.object := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  change (multiply R p L 1).app V s=s
  rw [apply,map_one,one_smul]
lemma mul (r t : R) : multiply R p L r ≫ multiply R p L t=multiply R p L (t*r) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  change (multiply R p L t).app V ((multiply R p L r).app V s)=
    (multiply R p L (t*r)).app V s
  rw [apply,apply,apply,map_mul,mul_smul]

/-- Every unit in the ORIGINAL coefficient ring gives an actual line
sheaf automorphism with its genuine inverse coefficient action. -/
@[expose] def iso (u : Rˣ) : L.object ≅ L.object where
  hom := multiply R p L (u:R)
  inv := multiply R p L ((u⁻¹:Rˣ):R)
  hom_inv_id := by rw [mul]; simpa only [Units.inv_mul] using one R p L
  inv_hom_id := by rw [mul]; simpa only [Units.mul_inv] using one R p L

local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R p L ⊤
lemma hom_section (u : Rˣ) (s : Γ(L.object,⊤)) : (iso R p L u).hom.app ⊤ s=(u:R) • s :=
  apply R p L (u:R) ⊤ s
end OriginalCoefficientUnitIso318
