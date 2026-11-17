module
public import DualNumberPointedKernel318
public import UnitCocycleRefinement318
public section
noncomputable section
namespace UnitCocycleSchemeRefinement318
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
lemma restrict_appLE {V W : Y.Opens} (h : V ≤ W) {V' W' : X.Opens} (h' : V' ≤ W')
    (hV : V' ≤ f ⁻¹ᵁ V) (hW : W' ≤ f ⁻¹ᵁ W) (a : Γ(Y,W)ˣ) :
    UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units X).obj h'
      (Units.map (f.appLE W W' hW).hom.toMonoidHom a) =
    Units.map (f.appLE V V' hV).hom.toMonoidHom
      (UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units Y).obj h a) := by
  apply Units.ext
  exact AdditiveCocycleRefinement318.restrict_appLE f h h' hV hW a.val
variable {ι : Type u} (U : ι → Y.Opens) (V : ι → X.Opens) (hV : ∀ a, V a ≤ f ⁻¹ᵁ U a)
@[expose] def cocycle
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units Y).obj U) :
    UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj V where
  transition a b := Units.map (f.appLE (U a ⊓ U b) (V a ⊓ V b)
    (inf_le_inf (hV a) (hV b))).hom.toMonoidHom (c.transition a b)
  diagonal a := by rw [c.diagonal, map_one]
  triple a b d := by
    rw [restrict_appLE f inf_le_left inf_le_left
      (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d)),
      restrict_appLE f (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d)),
      restrict_appLE f (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d))]
    let φ : Γ(Y, U a ⊓ U b ⊓ U d)ˣ →* Γ(X, V a ⊓ V b ⊓ V d)ˣ :=
      Units.map (f.appLE (U a ⊓ U b ⊓ U d) (V a ⊓ V b ⊓ V d)
        (inf_le_inf (inf_le_inf (hV a) (hV b)) (hV d))).hom.toMonoidHom
    have ht :
        (UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units Y).obj
          inf_le_left (c.transition a b) : Γ(Y, U a ⊓ U b ⊓ U d)ˣ) *
        UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units Y).obj
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c.transition b d) =
        UnitTransitionCocycle318.restrict (StructureUnitsSheaf318.units Y).obj
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c.transition a d) :=
      c.triple a b d
    exact (φ.map_mul _ _).symm.trans (congrArg φ ht)
lemma refine_full
    (c : UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units Y).obj U) :
    UnitCocycleRefinement318.refine
      (cocycle f U (fun a => f ⁻¹ᵁ U a) (fun _ => le_rfl) c) V id hV = cocycle f U V hV c := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro a b
  apply Units.ext
  change (X.presheaf.map (homOfLE (inf_le_inf (hV a) (hV b))).op)
    (f.appLE (U a ⊓ U b) ((f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b))
      (show (f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b) ≤ f ⁻¹ᵁ (U a ⊓ U b) from le_rfl) (c.transition a b).val) = _
  exact congrArg (fun k => k (c.transition a b).val)
    (show f.appLE (U a ⊓ U b) ((f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b))
      (show (f ⁻¹ᵁ U a) ⊓ (f ⁻¹ᵁ U b) ≤ f ⁻¹ᵁ (U a ⊓ U b) from le_rfl) ≫
      X.presheaf.map (homOfLE (inf_le_inf (hV a) (hV b))).op =
        f.appLE (U a ⊓ U b) (V a ⊓ V b) (inf_le_inf (hV a) (hV b)) by rw [Scheme.Hom.appLE_map])
end UnitCocycleSchemeRefinement318
