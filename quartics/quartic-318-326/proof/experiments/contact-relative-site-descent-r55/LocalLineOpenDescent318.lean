module
public import LocalChartTransition318
public import OpenSchemeGluing318
public section
noncomputable section
namespace LocalLineOpenDescent318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (L : ∀ i, LineSheafClass318.Line (U i).toScheme)
  (D : LocalChartTransition318.Data U (fun i => (L i).object))

/-- Actual original line sheaves with their own original local pair/triple
transitions glue on the original arbitrary scheme. Direct-image and over-open
coherence, sheaf object gluing and global frame refinement are all derived. -/
@[expose] def line (hcover : (⊤ : X.Opens) ≤ iSup U) : LineSheafClass318.Line X :=
  OpenChartLineEffectivity318.line U L (OpenSchemeTransition318.overData (LocalChartTransition318.ambientData D)) hcover

@[expose] def comparison (hcover : (⊤ : X.Opens) ≤ iSup U) (i : ι) :
    (line U L D hcover).object.restrict (U i).ι ≅ (L i).object :=
  OpenChartLineEffectivity318.comparison U L (OpenSchemeTransition318.overData (LocalChartTransition318.ambientData D)) hcover i

/-- The original global-to-local comparison on an actual subchart,
with the original restriction path retained. -/
@[expose] def overlapComparison (hcover : (⊤ : X.Opens) ≤ iSup U)
    (i : ι) (V : X.Opens) (h : V ≤ U i) :
    (line U L D hcover).object.restrict V.ι ≅ (L i).object.restrict (X.homOfLE h) :=
  OpenSheafRestrictionCompatibility318.path (line U L D hcover).object h ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso (comparison U L D hcover i)

lemma overlapComparison_eq (hcover : (⊤ : X.Opens) ≤ iSup U)
    (i : ι) (V : X.Opens) (h : V ≤ U i) :
    overlapComparison U L D hcover i V h =
      OpenSheafRestrictionCompatibility318.schemeRestrict
        (OpenSchemeGluing318.comparison (LocalChartTransition318.ambientData D) i) h ≪≫
      OpenChartModuleImages318.subchartRecovery U (fun i => (L i).object) i V h := by
  apply Iso.ext
  simp only [overlapComparison, comparison, OpenChartLineEffectivity318.comparison,
    OpenChartModuleImages318.comparison, OpenChartModuleImages318.subchartRecovery,
    OpenSheafRestrictionCompatibility318.schemeRestrict, OpenSheafRestrictionCompatibility318.path,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_app_assoc]

/-- The displayed global line comparisons recover the unchanged original
Fi-only transition on the whole original pair intersection. -/
lemma transition_recovered (hcover : (⊤ : X.Opens) ≤ iSup U) (i j : ι) :
    overlapComparison U L D hcover i (U i ⊓ U j) inf_le_left ≪≫ D.transition i j =
      overlapComparison U L D hcover j (U i ⊓ U j) inf_le_right := by
  rw [overlapComparison_eq, overlapComparison_eq]
  have h := OpenSchemeGluing318.transition_recovered (LocalChartTransition318.ambientData D) i j
  have hh := congrArg (fun e => e ≪≫
    OpenChartModuleImages318.subchartRecovery U (fun i => (L i).object) j (U i ⊓ U j)
      inf_le_right) h
  apply Iso.ext
  simpa only [LocalChartTransition318.ambientData, LocalChartTransition318.ambientTransition,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg Iso.hom hh

include D in
/-- Original local line descent data is effective on the actual open cover.
No ambient, over-open, scalar or object-gluing law is an extra premise. -/
theorem effective (hcover : (⊤ : X.Opens) ≤ iSup U) :
    ∃ (K : LineSheafClass318.Line X), ∀ i, Nonempty (K.object.restrict (U i).ι ≅ (L i).object) :=
  ⟨line U L D hcover, fun i => ⟨comparison U L D hcover i⟩⟩
end LocalLineOpenDescent318
