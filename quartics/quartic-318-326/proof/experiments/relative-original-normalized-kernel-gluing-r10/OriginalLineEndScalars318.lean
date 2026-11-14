module
public import OriginalLineEndCoordinates318
public section
noncomputable section
namespace OriginalLineEndScalars318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318 ModuleLocalGluing318
open OriginalLineEndCoordinates318
universe u
variable {X : Scheme.{u}} (L : Line X) (a : L.object ⟶ L.object)

lemma compatible : TopCat.Presheaf.IsCompatible X.presheaf L.opens
    (fun i => coefficient L a i (L.opens i) le_rfl) := by
  intro i j
  rw [natural,natural]
  exact independent L a i j _ inf_le_left inf_le_right

/-- Actual local endomorphism coefficients glue on every whole overlap,
without integrality, reducedness or existence of a global frame. -/
@[expose] def scalar : Γ(X,⊤) :=
  (TopCat.Sheaf.existsUnique_gluing' X.sheaf L.opens ⊤
    (fun _ => homOfLE le_top) L.cover
    (fun i => coefficient L a i (L.opens i) le_rfl) (compatible L a)).choose
lemma restrict_scalar (i : L.Index) :
    X.presheaf.map (homOfLE (show L.opens i≤⊤ from le_top)).op (scalar L a)=
      coefficient L a i (L.opens i) le_rfl :=
  (TopCat.Sheaf.existsUnique_gluing' X.sheaf L.opens ⊤
    (fun _ => homOfLE le_top) L.cover
    (fun i => coefficient L a i (L.opens i) le_rfl) (compatible L a)).choose_spec.1 i
lemma subopen_scalar (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :
    X.presheaf.map (homOfLE (show V≤⊤ from le_top)).op (scalar L a)=coefficient L a i V hV := by
  rw [←natural L a i (L.opens i) V le_rfl hV,←restrict_scalar]
  exact (Functor.map_comp_apply X.presheaf _ _ _).symm

lemma map_eq : a=ModuleScalar318.map L.object (scalar L a) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply ModuleLocalGluing318.ext_value L.cover V
  intro i
  have ha := congrArg (fun f => f s)
    (a.mapPresheaf.naturality (homOfLE (show V⊓L.opens i≤V from inf_le_left)).op)
  have hb := congrArg (fun f => f s)
    ((ModuleScalar318.map L.object (scalar L a)).mapPresheaf.naturality
      (homOfLE (show V⊓L.opens i≤V from inf_le_left)).op)
  change a.app _ (res L.object inf_le_left s)=res L.object inf_le_left (a.app V s) at ha
  change (ModuleScalar318.map L.object (scalar L a)).app _ (res L.object inf_le_left s)=
    res L.object inf_le_left ((ModuleScalar318.map L.object (scalar L a)).app V s) at hb
  rw [←ha,←hb,value L a i _ inf_le_right,ModuleScalar318.map_apply,subopen_scalar]

lemma scalar_map (r : Γ(X,⊤)) : scalar L (ModuleScalar318.map L.object r)=r := by
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf L.opens ⊤
    (fun _ => homOfLE le_top) L.cover
  intro i
  rw [restrict_scalar]
  exact unique L _ i (L.opens i) le_rfl _ (fun s => ModuleScalar318.map_apply L.object r _ s)

/-- Every endomorphism of an arbitrary original line is multiplication
by a UNIQUE actual global regular function. -/
@[expose] def equivalence : (L.object ⟶ L.object) ≃ Γ(X,⊤) where
  toFun := scalar L
  invFun := ModuleScalar318.map L.object
  left_inv a := (map_eq L a).symm
  right_inv := scalar_map L
end OriginalLineEndScalars318
