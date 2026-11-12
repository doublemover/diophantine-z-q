module
public import OriginalLineAutomorphismUnits318
public section
noncomputable section
namespace OriginalLineIsomUnitTorsor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (L M : Line X)

@[expose] def act (u : Γ(X,⊤)ˣ) (e : L.object ≅ M.object) : L.object ≅ M.object :=
  OriginalLineAutomorphismUnits318.iso L u ≪≫ e
@[expose] def ratio (e d : L.object ≅ M.object) : Γ(X,⊤)ˣ :=
  OriginalLineAutomorphismUnits318.value L (d ≪≫ e.symm)
lemma ratio_act (e d : L.object ≅ M.object) : act L M (ratio L M e d) e=d := by
  rw [act,ratio,OriginalLineAutomorphismUnits318.value_iso]
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
lemma act_ratio (u : Γ(X,⊤)ˣ) (e : L.object ≅ M.object) : ratio L M e (act L M u e)=u := by
  have h : act L M u e ≪≫ e.symm=OriginalLineAutomorphismUnits318.iso L u := by
    apply Iso.ext
    simp only [act,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [ratio,h,OriginalLineAutomorphismUnits318.iso_value]

/-- Given ONE actual isomorphism between two arbitrary original lines,
all actual isomorphisms are classified by units, including both inverses. -/
@[expose] def equivalence (e : L.object ≅ M.object) : Γ(X,⊤)ˣ ≃ (L.object ≅ M.object) where
  toFun u := act L M u e
  invFun d := ratio L M e d
  left_inv u := act_ratio L M u e
  right_inv d := ratio_act L M e d

lemma actual_map (e d : L.object ≅ M.object) :
    ModuleScalar318.map L.object (ratio L M e d : Γ(X,⊤)) ≫ e.hom=d.hom :=
  congrArg Iso.hom (ratio_act L M e d)
lemma unique (e d : L.object ≅ M.object) (u : Γ(X,⊤)ˣ)
    (h : ModuleScalar318.map L.object (u:Γ(X,⊤)) ≫ e.hom=d.hom) :
    u=ratio L M e d := by
  have hi : act L M u e=d := Iso.ext h
  rw [←hi,act_ratio]
end OriginalLineIsomUnitTorsor318
