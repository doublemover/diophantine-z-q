module
public import ModuleGlobalSections318
public section
noncomputable section
namespace ModuleFrameDescent318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u}
    (U : ι → X.Opens) (hU : ⊤ ≤ iSup U)
include hU

/-- Every open cover supplies the basis of all subopens of its members. -/
theorem subopen_basis :
    Opens.IsBasis (Set.range (fun V : {V : X.Opens // ∃ i, V ≤ U i} => V.1)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  have hcover : x ∈ iSup U := hU (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hcover
  refine ⟨V ⊓ U i,⟨⟨V ⊓ U i,⟨i,inf_le_right⟩⟩,rfl⟩,⟨hx,hi⟩,inf_le_left⟩

/-- An actual module-sheaf map is an isomorphism if it is so on every subopen
of an actual open cover. -/
theorem isIso_of_cover (f : M ⟶ N)
    (hf : ∀ i, ∀ (V : X.Opens), V ≤ U i → IsIso (f.app V)) : IsIso f := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hi : IsIso (F.map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B:=fun V : {V : X.Opens // ∃ i, V ≤ U i} => V.1)
      (subopen_basis U hU)
    intro V
    obtain ⟨i,hi⟩ := V.property
    exact hf i V.1 hi
  letI := hi
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  exact (inferInstance : IsIso ((F.map f).hom.app (op V)))

variable (M)
    (s : ∀ i, Γ(M,U i)) (hs : TopCat.Presheaf.IsCompatible M.presheaf U s)

theorem gluedMap_on_subopen (i : ι) (V : X.Opens) (hV : V ≤ U i) (a : Γ(X,V)) :
    (ModuleGlobalSections318.gluedMap M U hU s hs).val.app (op V) a =
      a • M.presheaf.map (homOfLE hV).op (s i) := by
  have hg := congrArg (M.presheaf.map (homOfLE hV).op)
    (ModuleGlobalSections318.gluedTop_restrict M U hU s hs i)
  have hc := congrArg (fun k => k (ModuleGlobalSections318.gluedTop M U hU s hs))
    (M.presheaf.map_comp (homOfLE (show U i ≤ ⊤ from le_top)).op (homOfLE hV).op)
  have hr : M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (ModuleGlobalSections318.gluedTop M U hU s hs) =
      M.presheaf.map (homOfLE hV).op (s i) := hc.trans hg
  exact (ModuleGlobalSections318.ofTop_apply M _ V a).trans
    (congrArg (fun t : Γ(M,V) => a • t) hr)

/-- Compatible actual local generators glue to an actual global frame if they
generate freely on every subopen. All compatibility and local freeness inputs
are explicit; the global sheaf map and its invertibility are constructed. -/
theorem gluedMap_isIso
    (hfree : ∀ i, ∀ (V : X.Opens), ∀ (hV : V ≤ U i), Function.Bijective
      (fun a : Γ(X,V) => a • M.presheaf.map (homOfLE hV).op (s i))) :
    IsIso (ModuleGlobalSections318.gluedMap M U hU s hs) := by
  apply isIso_of_cover U hU
  intro i V hV
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a : Γ(X,V) =>
    (ModuleGlobalSections318.gluedMap M U hU s hs).val.app (op V) a)
  have heq : (fun a : Γ(X,V) =>
      (ModuleGlobalSections318.gluedMap M U hU s hs).val.app (op V) a) =
      (fun a : Γ(X,V) => a • M.presheaf.map (homOfLE hV).op (s i)) := by
    funext a
    exact gluedMap_on_subopen (M:=M) U hU s hs i V hV a
  rw [heq]
  exact hfree i V hV

@[expose] def gluedFrame
    (hfree : ∀ i, ∀ (V : X.Opens), ∀ (hV : V ≤ U i), Function.Bijective
      (fun a : Γ(X,V) => a • M.presheaf.map (homOfLE hV).op (s i))) :
    SheafOfModules.unit X.ringCatSheaf ≅ M := by
  letI := gluedMap_isIso (M:=M) U hU s hs hfree
  exact asIso (ModuleGlobalSections318.gluedMap M U hU s hs)
end ModuleFrameDescent318
