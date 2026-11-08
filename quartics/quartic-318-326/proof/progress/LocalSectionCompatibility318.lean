module
public import ModuleGlobalSections318
public section
noncomputable section
namespace LocalSectionCompatibility318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens) (s : Γ(M,U)) (t : Γ(M,V))
@[expose] def Agree : Prop :=
  M.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s =
    M.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op t

theorem symm (h : Agree M U V s t) : Agree M V U t s := by
  let P (W : X.Opens) := ∀ (hU : W ≤ U) (hV : W ≤ V),
    M.presheaf.map (homOfLE hU).op s=M.presheaf.map (homOfLE hV).op t
  have hc : P (U ⊓ V) := fun _ _ => h
  exact ((Eq.mp (congrArg P (inf_comm U V)) hc) inf_le_right inf_le_left).symm

theorem restrict (h : Agree M U V s t) (Z : X.Opens) (hZU : Z ≤ U) (hZV : Z ≤ V) :
    M.presheaf.map (homOfLE hZU).op s=M.presheaf.map (homOfLE hZV).op t := by
  let i := (homOfLE (le_inf hZU hZV)).op
  have h1 := congrArg (fun k => k s)
    (M.presheaf.map_comp (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op i)
  have h2 := congrArg (fun k => k t)
    (M.presheaf.map_comp (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op i)
  exact h1.trans ((congrArg (M.presheaf.map i) h).trans h2.symm)

theorem trans_of_inter_le (W : X.Opens) (r : Γ(M,W))
    (h1 : Agree M U V s t) (h2 : Agree M V W t r) (hV : U ⊓ W ≤ V) : Agree M U W s r :=
  (restrict M U V s t h1 (U ⊓ W) inf_le_left hV).trans
    (restrict M V W t r h2 (U ⊓ W) hV inf_le_right)

theorem refl : Agree M U U s s := rfl
end LocalSectionCompatibility318
