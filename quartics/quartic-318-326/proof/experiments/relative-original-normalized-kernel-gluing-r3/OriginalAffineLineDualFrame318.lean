module
public import FiniteProjectiveDualFrame318
public import OriginalLineAffineModel318
public section
noncomputable section
namespace OriginalAffineLineDualFrame318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Transport a finite identity decomposition by the actual additive
functor and specified object isomorphisms. -/
lemma transport_total {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {M N : C} {A B : D} (e : F.obj M ≅ A) (u : F.obj N ≅ B)
    {ι : Type*} [Fintype ι] (out : ι → M ⟶ N) (back : ι → N ⟶ M)
    (h : ∑ i, out i ≫ back i = 𝟙 M) :
    ∑ i, (e.inv ≫ F.map (out i) ≫ u.hom) ≫
      (u.inv ≫ F.map (back i) ≫ e.hom) = 𝟙 A := by
  calc
    _ = e.inv ≫ (∑ i, F.map (out i ≫ back i)) ≫ e.hom := by
      simp only [Functor.map_comp,Preadditive.comp_sum,Preadditive.sum_comp,
        Category.assoc,Iso.hom_inv_id_assoc]
    _ = e.inv ≫ F.map (𝟙 M) ≫ e.hom := by rw [← Functor.map_sum,h]
    _ = _ := by simp only [Functor.map_id,Category.id_comp,Iso.inv_hom_id]

variable (R : CommRingCat.{u}) (L : Line (Spec R))

/-- Projectivity of the SAME old section module follows from its already
proved finite presentation and flatness at every original stalk. -/
instance projective : Module.Projective R (OriginalLineAffineModel318.sections R L) := by
  letI := (OriginalLineAffineModel318.properties R L).1
  letI := (OriginalLineAffineModel318.properties R L).2.1
  exact FiniteProjectiveDualFrame318.projective_of_finitePresentation_flat R _

/-- A finite dual frame of the original section module; not a rank-one basis. -/
def moduleFrame : FiniteProjectiveDualFrame318.Frame R (OriginalLineAffineModel318.sections R L) := by
  letI := (OriginalLineAffineModel318.properties R L).1
  exact FiniteProjectiveDualFrame318.frame R _

/-- Actual sheaf maps to/from the structure line on the original affine
scheme, through the unchanged tilde counit. -/
def out (i : Fin (moduleFrame R L).n) : L.object ⟶ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (OriginalLineAffineModel318.canonicalIso R L).inv ≫
    (tilde.functor R).map (ModuleCat.ofHom ((moduleFrame R L).out i)) ≫ tildeSelf.hom

def back (i : Fin (moduleFrame R L).n) : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ L.object :=
  tildeSelf.inv ≫ (tilde.functor R).map (ModuleCat.ofHom ((moduleFrame R L).back i)) ≫
    (OriginalLineAffineModel318.canonicalIso R L).hom

/-- The sum of these genuine structure-line factorizations is the identity
of the SAME actual line sheaf. -/
lemma total : ∑ i, out R L i ≫ back R L i = 𝟙 L.object := by
  apply transport_total (tilde.functor R)
    (OriginalLineAffineModel318.canonicalIso R L) tildeSelf
    (fun i => ModuleCat.ofHom ((moduleFrame R L).out i))
    (fun i => ModuleCat.ofHom ((moduleFrame R L).back i))
  apply ModuleCat.hom_ext
  change (∑ i, ((moduleFrame R L).back i).comp ((moduleFrame R L).out i)) = LinearMap.id
  exact (moduleFrame R L).total
end OriginalAffineLineDualFrame318
