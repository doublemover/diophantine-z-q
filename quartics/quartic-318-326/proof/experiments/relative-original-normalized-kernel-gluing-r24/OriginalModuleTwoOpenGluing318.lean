module
public import ModuleGlobalSections318
public section
noncomputable section
namespace OriginalModuleTwoOpenGluing318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)

/-- Actual section gluing on a genuine binary whole-open cover, retaining
the original two restriction maps, including the swapped intersection. -/
lemma exists_gluing (hcover : U ⊔ V = ⊤) (a : Γ(M,U)) (b : Γ(M,V))
    (hab : M.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a =
      M.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b) :
    ∃ s : Γ(M,⊤),
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = a ∧
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s = b := by
  let W : ULift.{u} (Fin 2) → X.Opens := fun i => ![U,V] i.down
  have hc : ⊤ ≤ iSup W := by
    exact (le_of_eq hcover.symm).trans (sup_le (le_iSup W ⟨0⟩) (le_iSup W ⟨1⟩))
  let basePieces : ∀ i : Fin 2, Γ(M, (![U,V] i)) :=
    Fin.cases a (Fin.cases b (fun i => Fin.elim0 i))
  let pieces : ∀ i, Γ(M,W i) := fun i => basePieces i.down
  have hswap : M.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op b =
      M.presheaf.map (homOfLE inf_le_right : V ⊓ U ⟶ U).op a := by
    have h := congrArg (fun t => M.presheaf.map (eqToHom (inf_comm V U)).op t) hab.symm
    have hb : (homOfLE inf_le_right : U ⊓ V ⟶ V).op ≫
        (eqToHom (inf_comm V U)).op =
        (homOfLE inf_le_left : V ⊓ U ⟶ V).op := Subsingleton.elim _ _
    have ha : (homOfLE inf_le_left : U ⊓ V ⟶ U).op ≫
        (eqToHom (inf_comm V U)).op =
        (homOfLE inf_le_right : V ⊓ U ⟶ U).op := Subsingleton.elim _ _
    simpa only [← Functor.map_comp_apply,hb,ha] using h
  have hp : TopCat.Presheaf.IsCompatible M.presheaf W pieces := by
    intro i j
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · rfl
    · exact hab
    · exact hswap
    · rfl
  refine ⟨ModuleGlobalSections318.gluedTop M W hc pieces hp,?_,?_⟩
  · exact ModuleGlobalSections318.gluedTop_restrict M W hc pieces hp ⟨0⟩
  · exact ModuleGlobalSections318.gluedTop_restrict M W hc pieces hp ⟨1⟩
end OriginalModuleTwoOpenGluing318
