module
public import OriginalLineAutomorphismLocal318
public import ModuleLocalGluing318
public section
noncomputable section
namespace OriginalLineAutomorphismScalar318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open OriginalLineAutomorphismLocal318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L : Line X) (f : L.object ≅ L.object)

/-- The original local automorphism coefficients glue in the actual sheaf
of structure units. This is a genuine global invertible regular function. -/
@[expose] def scalar : Γ(X,⊤)ˣ :=
  Classical.choose (TopCat.Sheaf.existsUnique_gluing' (StructureUnitsSheaf318.units X)
    L.opens ⊤ (fun _ => homOfLE le_top) L.cover
    (fun i => localScalar L f i (L.opens i) le_rfl) (localScalars_compatible L f))

lemma scalar_restrict (i : L.Index) :
    Units.map (X.presheaf.map (homOfLE (show L.opens i ≤ ⊤ from le_top)).op).hom.toMonoidHom
        (scalar L f) = localScalar L f i (L.opens i) le_rfl := by
  have hh := (Classical.choose_spec
    (TopCat.Sheaf.existsUnique_gluing' (StructureUnitsSheaf318.units X)
      L.opens ⊤ (fun _ => homOfLE le_top) L.cover
      (fun i => localScalar L f i (L.opens i) le_rfl) (localScalars_compatible L f))).1 i
  exact hh

lemma scalar_subopen (i : L.Index) (W : X.Opens) (h : W ≤ L.opens i) :
    X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (scalar L f).val =
      (localScalar L f i W h).val := by
  calc
    _ = X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE (show L.opens i ≤ ⊤ from le_top)).op (scalar L f).val) := by
      rw [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    _ = X.presheaf.map (homOfLE h).op (localScalar L f i (L.opens i) le_rfl).val :=
      congrArg (X.presheaf.map (homOfLE h).op) (congrArg Units.val (scalar_restrict L f i))
    _ = (localScalar L f i W h).val := congrArg Units.val (localScalar_restrict L f i W h)

/-- Every original line automorphism acts on every section over every open
by restriction of the same actual global unit. -/
lemma scalar_action (W : X.Opens) (s : Γ(L.object,W)) :
    f.hom.app W s =
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (scalar L f).val • s := by
  apply ModuleLocalGluing318.ext_value (N := L.object) (U := L.opens) L.cover W
  intro i
  let V := W ⊓ L.opens i
  change L.object.presheaf.map (homOfLE (show V ≤ W from inf_le_left)).op (f.hom.app W s) =
    L.object.presheaf.map (homOfLE (show V ≤ W from inf_le_left)).op
      (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (scalar L f).val • s)
  have hn : L.object.presheaf.map (homOfLE (show V ≤ W from inf_le_left)).op
      (f.hom.app W s) = f.hom.app V
        (L.object.presheaf.map (homOfLE (show V ≤ W from inf_le_left)).op s) :=
    (congrArg (fun k => k s)
      (f.hom.mapPresheaf.naturality (homOfLE (show V ≤ W from inf_le_left)).op)).symm
  rw [hn, Scheme.Modules.map_smul, localScalar_action L f i V inf_le_right,
    ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
    scalar_subopen L f i V inf_le_right]

/-- The scalar is uniquely determined by the actual original sheaf action.
The proof uses the whole original frame cover. -/
lemma scalar_unique (a : Γ(X,⊤)ˣ)
    (ha : ∀ (W : X.Opens) (s : Γ(L.object,W)), f.hom.app W s =
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a.val • s) : scalar L f = a := by
  apply TopCat.Sheaf.eq_of_locally_eq' (StructureUnitsSheaf318.units X)
    L.opens ⊤ (fun _ => homOfLE le_top) L.cover
  intro i
  exact (scalar_restrict L f i).trans
    (localScalar_unique L f i (L.opens i) le_rfl
      (Units.map (X.presheaf.map (homOfLE le_top).op).hom.toMonoidHom a)
      (ha (L.opens i)))
end OriginalLineAutomorphismScalar318
