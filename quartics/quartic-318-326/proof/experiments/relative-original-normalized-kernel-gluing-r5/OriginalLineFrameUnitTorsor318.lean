module
public import StructureLineUnitLaws318
public import LineSheafClass318
public section
noncomputable section
namespace OriginalLineFrameUnitTorsor318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (L : Line X)
abbrev Frames := SheafOfModules.unit X.ringCatSheaf ≅ L.object

/-- The actual global unit acts on the source of the full frame map. -/
@[expose] def act (u : Γ(X,⊤)ˣ) (e : Frames L) : Frames L :=
  StructureLineAutomorphisms318.iso X u ≪≫ e
lemma one_act (e : Frames L) : act L 1 e=e := by
  rw [act,StructureLineUnitLaws318.iso_one]
  exact Iso.refl_trans e
lemma mul_act (u v : Γ(X,⊤)ˣ) (e : Frames L) : act L (u*v) e=act L u (act L v e) := by
  apply Iso.ext
  simp only [act,StructureLineUnitLaws318.iso_mul,Iso.trans_hom,Category.assoc]

/-- Exact ratio of two actual frames, retaining their entire sheaf
composition and the inverse map, not only line isomorphism classes. -/
@[expose] def ratio (e d : Frames L) : Γ(X,⊤)ˣ :=
  StructureLineAutomorphisms318.value X (d ≪≫ e.symm)
lemma ratio_act (e d : Frames L) : act L (ratio L e d) e=d := by
  rw [act,ratio,StructureLineAutomorphisms318.value_iso]
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
lemma act_ratio (u : Γ(X,⊤)ˣ) (e : Frames L) : ratio L e (act L u e)=u := by
  have he : act L u e ≪≫ e.symm=StructureLineAutomorphisms318.iso X u := by
    apply Iso.ext
    simp only [act,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [ratio,he,StructureLineAutomorphisms318.iso_value]

/-- Whenever one actual frame exists, every other frame is obtained by
one UNIQUE global unit. Existence of a frame is not assumed globally. -/
lemma existsUnique (e d : Frames L) : ∃! u : Γ(X,⊤)ˣ,act L u e=d := by
  refine ⟨ratio L e d,ratio_act L e d,?_⟩
  intro u hu
  rw [←hu,act_ratio]
end OriginalLineFrameUnitTorsor318
