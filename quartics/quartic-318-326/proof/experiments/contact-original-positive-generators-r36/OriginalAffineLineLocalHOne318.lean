module
public import OriginalAffineLineDualFrame318
public import ExtFiniteRetractVanishing318
public import LocalAffineStructureHOne318
public section
noncomputable section
namespace OriginalAffineLineLocalHOne318
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian LineSheafClass318
open LocalSheafCohomologySections318
open scoped BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [IsDomain R] (L : Line (Spec R))

/-- The actual original line sheaf, with only scalar multiplication forgotten. -/
abbrev additiveLine : ASheaf (X:=Spec R) :=
  (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj L.object

/-- Forgetting the structure-line scalar action gives the original additive
structure sheaf, including its actual restriction maps. -/
def additiveUnitIso :
    (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf) ≅ StructureAdditiveSheaf318.sheaf (Spec R) :=
  Iso.refl _

/-- Every original affine line is acyclic in degree one on every affine
open of its actual affine scheme. The proof uses a genuine finite identity
decomposition, not an assertion that the line is globally trivial. -/
theorem eq_zero (U : (Spec R).Opens) (hU : IsAffineOpen U)
    (x : (additiveLine R L).H' 1 U) : x = 0 := by
  let F := SheafOfModules.toSheaf (Spec R).ringCatSheaf
  let e := additiveUnitIso R
  let a (i : Fin (OriginalAffineLineDualFrame318.moduleFrame R L).n) :=
    F.map (OriginalAffineLineDualFrame318.out R L i) ≫ e.hom
  let b (i : Fin (OriginalAffineLineDualFrame318.moduleFrame R L).n) :=
    e.inv ≫ F.map (OriginalAffineLineDualFrame318.back R L i)
  have ht : ∑ i, a i ≫ b i = 𝟙 (additiveLine R L) := by
    simp only [a,b,Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,
      ← Functor.map_sum,OriginalAffineLineDualFrame318.total,Functor.map_id]
  exact ExtFiniteRetractVanishing318.eq_zero
    (fun _ : Fin (OriginalAffineLineDualFrame318.moduleFrame R L).n =>
      StructureAdditiveSheaf318.sheaf (Spec R)) a b ht 1
    (fun _ y => LocalAffineStructureHOne318.eq_zero U hU y) x
end OriginalAffineLineLocalHOne318
