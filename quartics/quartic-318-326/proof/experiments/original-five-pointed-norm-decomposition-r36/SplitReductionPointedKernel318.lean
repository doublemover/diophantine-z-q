module
public import ModuleScalarPullback318
public import OriginalHOnePointedMaps318
public section
noncomputable section
namespace SplitReductionPointedKernel318
open AlgebraicGeometry CategoryTheory PointedLineDeformation318
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (r : X ⟶ X₀) (hr : i ≫ r = 𝟙 X₀)
include hr in
lemma scalar_reduction (a : Γ(X₀,⊤)) : i.appTop (r.appTop a) = a := by
  change (r.appTop ≫ i.appTop) a = a
  rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  all_goals rfl
/-- For a split reduction, lift the exact global unit measuring the discrepancy
of two special-fiber frames, and correct the supplied original line iso by that
actual scalar automorphism. No classification of line bundles is used. -/
@[expose] def pointedIsoOfIso (L M : Deformation i) (e : L.line.object ≅ M.line.object) :
    PointedIso i L M := by
  let δ := L.trivialization.symm ≪≫ (Scheme.Modules.pullback i).mapIso e ≪≫ M.trivialization
  let u : Γ(X₀,⊤)ˣ := UnitSheafScalar318.unit δ.symm
  let a : Γ(X,⊤)ˣ := Units.map r.appTop.hom.toMonoidHom u
  refine ⟨ModuleScalarPullback318.unitIso L.line.object a ≪≫ e, ?_⟩
  change (Scheme.Modules.pullback i).map (ModuleScalar318.map L.line.object a.val ≫ e.hom) ≫
    M.trivialization.hom = L.trivialization.hom
  rw [Functor.map_comp, Category.assoc, ModuleScalarPullback318.pullback_map]
  change ModuleScalar318.map ((Scheme.Modules.pullback i).obj L.line.object)
      (i.appTop (r.appTop u.val)) ≫
      ((Scheme.Modules.pullback i).map e.hom ≫ M.trivialization.hom) = L.trivialization.hom
  rw [scalar_reduction i r hr, ModuleScalar318.natural, ModuleScalar318.unit_eq]
  rw [← UnitSheafScalar318.hom_multiply δ.symm]
  change ((Scheme.Modules.pullback i).map e.hom ≫ M.trivialization.hom) ≫ δ.inv = _
  simp only [δ, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, e.hom_inv_id, Functor.map_id, Category.id_comp]
  all_goals rw [(Scheme.Modules.pullback i).map_id, Category.id_comp]
include r hr in
/-- Forgetting the special-fiber trivialization is injective because the actual
retraction lifts every global-unit correction. -/
lemma forget_injective : Function.Injective (forget i) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M =>
      obtain ⟨e⟩ := (LineSheafClass318.classOf_eq_iff L.line M.line).1 hab
      exact (classOf_eq_iff i L M).2 ⟨pointedIsoOfIso i r hr L M e⟩
/-- The kernel is the EXISTING line-class carrier with its actual restriction
condition. No tangent or represented Picard object has been introduced. -/
abbrev Kernel := {c : LineSheafClass318.Class X //
  LineSheafPullback318.pullback i c = LineSheafUnit318.unitClass X₀}
@[expose] def kernelMap (c : PointedLineDeformation318.Class i) : Kernel i :=
  ⟨forget i c, special_fiber_trivial i c⟩
include r hr in
lemma kernelMap_injective : Function.Injective (kernelMap i) := by
  intro a b h
  exact forget_injective i r hr (congrArg Subtype.val h)
lemma kernelMap_surjective : Function.Surjective (kernelMap i) := by
  rintro ⟨c,hc⟩
  induction c using LineSheafClass318.induction with
  | h L =>
    obtain ⟨t⟩ := (LineSheafUnit318.eq_unitClass_iff (LineSheafPullback318.line i L)).1 hc
    refine ⟨classOf i ⟨L,t⟩, ?_⟩
    apply Subtype.ext
    rfl
/-- Actual pointed deformations for a split reduction are exactly the kernel
of the original restriction on actual line-sheaf isomorphism classes. -/
@[expose] def equivalence : PointedLineDeformation318.Class i ≃ Kernel i :=
  Equiv.ofBijective (kernelMap i) ⟨kernelMap_injective i r hr, kernelMap_surjective i⟩
lemma equivalence_val (c : PointedLineDeformation318.Class i) :
    (equivalence i r hr c).val = forget i c := rfl
end SplitReductionPointedKernel318
