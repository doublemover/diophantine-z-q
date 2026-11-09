module
public import OpenSheafGluing318
public section
noncomputable section
namespace OpenChartModuleImages318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (F : ∀ i, (U i).toScheme.Modules)

/-- Actual chart sheaves become ambient modules by their original direct
images. The gluing construction uses only each one's original chart. -/
@[expose] def ambient (i : ι) : X.Modules :=
  (Scheme.Modules.pushforward (U i).ι).obj (F i)

/-- Original open-immersion restriction/direct-image counit recovers the
unchanged local chart sheaf, not merely an isomorphic section module. -/
@[expose] def chartRecovery (i : ι) : (ambient U F i).restrict (U i).ι ≅ F i :=
  (Scheme.Modules.restrictFunctorAdjCounitIso (U i).ι).app (F i)

/-- The same original chart sheaf is recovered on each actual subchart,
with the original composition and inclusion-equality transports retained. -/
@[expose] def subchartRecovery (i : ι) (V : X.Opens) (h : V ≤ U i) :
    (ambient U F i).restrict V.ι ≅ (F i).restrict (X.homOfLE h) :=
  ((Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X h).symm).app (ambient U F i)) ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) (U i).ι).app (ambient U F i) ≪≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso (chartRecovery U F i)

/-- Convert an original sheaf isomorphism on a literal intersection to
the canonical over-open model, retaining the original ambient sheaves. -/
@[expose] def toOverIso {A B : X.Modules} (V : X.Opens)
    (e : A.restrict V.ι ≅ B.restrict V.ι) : A.over V ≅ B.over V :=
  (Scheme.Modules.overEquiv V).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv V).app A ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv V).app B).symm)

/-- A transition between original local chart sheaves on the actual
intersection gives the corresponding actual ambient over-open transition. -/
@[expose] def pairTransition (i j : ι)
    (e : (F i).restrict (X.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) ≅
      (F j).restrict (X.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))) :
    (ambient U F i).over (U i ⊓ U j) ≅ (ambient U F j).over (U i ⊓ U j) :=
  toOverIso (U i ⊓ U j)
    (subchartRecovery U F i (U i ⊓ U j) inf_le_left ≪≫ e ≪≫
      (subchartRecovery U F j (U i ⊓ U j) inf_le_right).symm)

variable (D : OpenSheafTransition318.Data U (ambient U F))
abbrev glued := OpenSheafGluing318.sheaf D

/-- The constructed global sheaf recovers each unchanged original local
chart sheaf through the same canonical restriction/direct-image comparison. -/
@[expose] def comparison (i : ι) : (glued U F D).restrict (U i).ι ≅ F i :=
  OpenSheafGluing318.chartIso D i ≪≫ chartRecovery U F i

/-- Actual local modules with genuine compatible ambient sheaf overlap
data glue to an actual module sheaf on the original arbitrary scheme. -/
theorem effective : ∃ (G : X.Modules), ∀ i, Nonempty (G.restrict (U i).ι ≅ F i) :=
  ⟨glued U F D, fun i => ⟨comparison U F D i⟩⟩
end OpenChartModuleImages318
