module
public import OriginalLineIsomUnitTorsor318
public section
noncomputable section
namespace OriginalLineIsomScalarCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineEndScalars318
universe u
variable {X : Scheme.{u}} (L M : Line X) (e : L.object ≅ M.object)

/-- The actual global scalar of an arbitrary line endomorphism is
unchanged by a full original line comparison. -/
lemma scalar_conjugation (a : L.object ⟶ L.object) :
    scalar M (e.inv ≫ a ≫ e.hom)=scalar L a := by
  have h : e.inv ≫ a ≫ e.hom=ModuleScalar318.map M.object (scalar L a) := by
    calc
      e.inv ≫ a ≫ e.hom=e.inv ≫ ModuleScalar318.map L.object (scalar L a) ≫ e.hom :=
        congrArg (fun k => e.inv ≫ k ≫ e.hom) (map_eq L a)
      _ = e.inv ≫ e.hom ≫ ModuleScalar318.map M.object (scalar L a) :=
        congrArg (fun k => e.inv ≫ k) (ModuleScalar318.natural (scalar L a) e.hom)
      _ = _ := by simp only [←Category.assoc,e.inv_hom_id,Category.id_comp]
  rw [h,scalar_map]

lemma automorphism_conjugation (a : L.object ≅ L.object) :
    OriginalLineAutomorphismUnits318.value M (e.symm ≪≫ a ≪≫ e)=
      OriginalLineAutomorphismUnits318.value L a := by
  apply Units.ext
  exact scalar_conjugation L M e a.hom

/-- The ratio does not depend on a presentation of the common target:
postcomposition preserves the actual unit relating two original maps. -/
lemma target_comparison (N : Line X) (h : M.object ≅ N.object)
    (a b : L.object ≅ M.object) :
    OriginalLineIsomUnitTorsor318.ratio L N (a ≪≫ h) (b ≪≫ h)=
      OriginalLineIsomUnitTorsor318.ratio L M a b := by
  have he : (b ≪≫ h) ≪≫ (a ≪≫ h).symm=b ≪≫ a.symm := by
    apply Iso.ext
    simp only [Iso.trans_hom,Iso.symm_hom,Iso.trans_inv,Category.assoc,
      h.hom_inv_id_assoc]
  rw [OriginalLineIsomUnitTorsor318.ratio,he]
  rfl
end OriginalLineIsomScalarCompatibility318
