module
public import OpenModuleSheafGluing318
public import LineSheafClass318
public section
noncomputable section
namespace OpenModuleGluedSheaf318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318 OpenModuleChartRecovery318 OpenModulePresheaf318 OpenModuleSheafGluing318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : Data U M)

/-- The matching-family presheaf has the actual sheaf gluing property. -/
lemma isSheaf : (presheaf D).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (presheaf D)).mpr
  intro κ V s hs
  have hall : ∀ k l (Z : X.Opens) (hk : Z ≤ V k) (hl : Z ≤ V l),
      (OpenModuleTransition318.restrict D) hk (s k) = (OpenModuleTransition318.restrict D) hl (s l) := by
    intro k l Z hk hl
    have hp : (OpenModuleTransition318.restrict D) inf_le_left (s k) = (OpenModuleTransition318.restrict D) inf_le_right (s l) := hs k l
    have h := congrArg ((OpenModuleTransition318.restrict D) (le_inf hk hl)) hp
    simpa only [restrict_restrict] using h
  refine ⟨glued D V (iSup V) (le_iSup V) le_rfl s hall, ?_, ?_⟩
  · intro k
    exact glued_restrict D V (iSup V) (le_iSup V) le_rfl s hall k
  · intro t ht
    exact glued_unique D V (iSup V) (le_iSup V) le_rfl s hall t ht

/-- The actual global module sheaf obtained by gluing the original local
modules and transition maps. Its sections are the explicit matching families. -/
@[expose] def sheaf : X.Modules where
  val := modulePresheaf D
  isSheaf := isSheaf D

lemma evaluate_add (i : ι) (W : X.Opens) (hi : W ≤ U i) (s t : (OpenModuleTransition318.sections D) W) :
    evaluate D i W hi (s + t) = evaluate D i W hi s + evaluate D i W hi t :=
  map_add _ _ _

lemma evaluate_smul (i : ι) (W : X.Opens) (hi : W ≤ U i) (a : Γ(X,W)) (s : (OpenModuleTransition318.sections D) W) :
    evaluate D i W hi (a • s) = a • evaluate D i W hi s := by
  change res (M i) (le_inf le_rfl hi)
    ((X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op a) • s.val i) = _
  rw [res, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  change (X.presheaf.map (𝟙 (op W)) a) • evaluate D i W hi s = _
  rw [Functor.map_id, ConcreteCategory.id_apply]

/-- The actual local comparison is linear over the same original section
ring, not merely an equivalence of underlying matching-family types. -/
@[expose] def chartLinearEquiv (i : ι) (W : X.Opens) (hi : W ≤ U i) :
    Γ(sheaf D,W) ≃ₗ[Γ(X,W)] Γ(M i,W) where
  toEquiv := chartEquiv D i W hi
  map_add' := evaluate_add D i W hi
  map_smul' := evaluate_smul D i W hi

/-- The chart comparison is an actual module-sheaf isomorphism on the
original site over the chart, with naturality on all actual subopens. -/
@[expose] def overIso (i : ι) : (sheaf D).over (U i) ≅ (M i).over (U i) :=
  (SheafOfModules.forget (X.ringCatSheaf.over (U i))).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (chartLinearEquiv D i V.unop.left (leOfHom V.unop.hom)).toModuleIso)
      (by
        intro V W f
        ext s
        exact (evaluate_natural D i (leOfHom V.unop.hom) (leOfHom f.unop.left) s).symm))

/-- The exact recovered chart object, now on the original open subscheme
through the canonical over-open/restriction comparison. -/
@[expose] def chartIso (i : ι) : (sheaf D).restrict (U i).ι ≅ (M i).restrict (U i).ι :=
  ((Scheme.Modules.overFunctorEquiv (U i)).app (sheaf D)).symm ≪≫
    (Scheme.Modules.overEquiv (U i)).functor.mapIso (overIso D i) ≪≫
      (Scheme.Modules.overFunctorEquiv (U i)).app (M i)

/-- Actual rank-one chart frames give a genuine global line on an
arbitrary scheme. Coverage is supplied explicitly and never inferred from
an arbitrary collection of compatible modules. -/
@[expose] def line (hcover : (⊤ : X.Opens) ≤ iSup U)
    (frames : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ (M i).restrict (U i).ι) :
    LineSheafClass318.Line X where
  object := sheaf D
  Index := ι
  opens := U
  cover := hcover
  frame i := frames i ≪≫ (chartIso D i).symm
end OpenModuleGluedSheaf318
