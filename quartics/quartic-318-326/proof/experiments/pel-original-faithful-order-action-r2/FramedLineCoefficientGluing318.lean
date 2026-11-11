module
public import LineFrameCocycle318
public import ModuleFrameDescent318
public section
noncomputable section
namespace FramedLineCoefficientGluing318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (e : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (r : ∀ i, Γ(X,U i))
  (hr : ∀ i j, X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (r i) =
    ((LineFrameCocycle318.cocycle M U e).transition i j).val *
      X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (r j))
@[expose] def localSection (i : ι) : Γ(M,U i) :=
  OpenLineFrameCoordinates318.frame M (U i) (e i) (U i) le_rfl (r i)
include hr in
lemma compatible : TopCat.Presheaf.IsCompatible M.presheaf U (localSection M U e r) := by
  intro i j
  rw [localSection,localSection,OpenLineFrameCoordinates318.natural,
    OpenLineFrameCoordinates318.natural,hr]
  exact LineFrameTransitions318.relation M U e i j (U i ⊓ U j) inf_le_left inf_le_right _

/-- Genuine global section obtained from regular coefficients satisfying
actual whole-overlap frame relations. The module sheaf is unchanged. -/
@[expose] def global (hU : (⊤ : X.Opens) ≤ ⨆ i,U i) : Γ(M,⊤) :=
  ModuleGlobalSections318.gluedTop M U hU (localSection M U e r) (compatible M U e r hr)
lemma global_restrict (hU : (⊤ : X.Opens) ≤ ⨆ i,U i) (i : ι) :
    M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op (global M U e r hr hU)=
      localSection M U e r i :=
  ModuleGlobalSections318.gluedTop_restrict M U hU (localSection M U e r)
    (compatible M U e r hr) i

/-- The actual global section morphism, with full local coefficients
specified on EVERY subopen, not only in point fibers. -/
@[expose] def sectionMap (hU : (⊤ : X.Opens) ≤ ⨆ i,U i) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  ModuleGlobalSections318.gluedMap M U hU (localSection M U e r) (compatible M U e r hr)
lemma sectionMap_subopen (hU : (⊤ : X.Opens) ≤ ⨆ i,U i)
    (i : ι) (V : X.Opens) (hV : V ≤ U i) (a : Γ(X,V)) :
    (sectionMap M U e r hr hU).app V a=
      OpenLineFrameCoordinates318.frame M (U i) (e i) V hV
        (a * X.presheaf.map (homOfLE hV).op (r i)) := by
  rw [sectionMap,ModuleFrameDescent318.gluedMap_on_subopen,
    localSection,OpenLineFrameCoordinates318.natural]
  exact (OpenLineFrameCoordinates318.frame M (U i) (e i) V hV).map_smul a _ |>.symm
/-- Uniqueness in the actual sheaf condition, retaining all original
restriction maps. -/
lemma global_unique (hU : (⊤ : X.Opens) ≤ ⨆ i,U i) (s : Γ(M,⊤))
    (hs : ∀ i, M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op s=
      localSection M U e r i) : s=global M U e r hr hU := by
  exact (Classical.choose_spec (TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf,M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U ⊤ (fun _ => homOfLE le_top) hU (localSection M U e r)
    (compatible M U e r hr))).2 s hs
end FramedLineCoefficientGluing318
