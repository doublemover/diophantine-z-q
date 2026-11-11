module
public import FamilyIntrinsicDifferentials318
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public section
noncomputable section
namespace ModuleGlobalSections318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} (M : X.Modules)

/-- A literal top-open section determines the actual compatible global section
of an O-module sheaf. -/
@[expose] def sectionOfTop (s : Γ(M,⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) (by
      intro U V i
      have h := congrArg (fun k => k s)
        (M.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op i)
      exact h.symm)

/-- The genuine O-linear morphism represented by a top-open section. -/
@[expose] def ofTop (s : Γ(M,⊤)) : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionOfTop M s)

theorem ofTop_one (s : Γ(M,⊤)) (U : X.Opens) :
    (ofTop M s).val.app (op U) (show Γ(X,U) from 1) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s :=
  congrArg (fun t => t.val (op U)) (M.unitHomEquiv.apply_symm_apply (sectionOfTop M s))

theorem ofTop_apply (s : Γ(M,⊤)) (U : X.Opens) (a : Γ(X,U)) :
    (ofTop M s).val.app (op U) a =
      a • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  let q : Γ(X,U) →ₗ[Γ(X,U)] Γ(M,U) := ((ofTop M s).val.app (op U)).hom
  have h : q (1:Γ(X,U)) = M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s :=
    ofTop_one M s U
  change q a = _
  calc
    q a = q (a • (1:Γ(X,U))) := by rw [smul_eq_mul,mul_one]
    _ = a • q 1 := q.map_smul a 1
    _ = _ := congrArg (fun t : Γ(M,U) => a • t) h

variable {ι : Type u} (U : ι → X.Opens) (hU : ⊤ ≤ iSup U)
    (s : ∀ i, Γ(M,U i)) (hs : TopCat.Presheaf.IsCompatible M.presheaf U s)

/-- Compatible actual local module sections on an actual open cover glue to an
actual top-open section, using the genuine sheaf condition. -/
@[expose] def gluedTop : Γ(M,⊤) :=
  Classical.choose (TopCat.Sheaf.existsUnique_gluing' (⟨M.presheaf,M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U ⊤ (fun _ => homOfLE le_top) hU s hs)

theorem gluedTop_restrict (i : ι) :
    M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (gluedTop M U hU s hs) = s i :=
  (Classical.choose_spec (TopCat.Sheaf.existsUnique_gluing' (⟨M.presheaf,M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U ⊤ (fun _ => homOfLE le_top) hU s hs)).1 i

@[expose] def gluedMap : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  ofTop M (gluedTop M U hU s hs)

theorem gluedMap_local (i : ι) (a : Γ(X,U i)) :
    (gluedMap M U hU s hs).val.app (op (U i)) a = a • s i := by
  exact (ofTop_apply M (gluedTop M U hU s hs) (U i) a).trans
    (congrArg (fun t : Γ(M,U i) => a • t) (gluedTop_restrict M U hU s hs i))
end ModuleGlobalSections318
