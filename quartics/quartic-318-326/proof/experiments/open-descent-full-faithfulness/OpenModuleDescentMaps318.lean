module
public import OpenModuleGluedSheaf318
public section
noncomputable section
namespace OpenModuleDescentMaps318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318 OpenModuleChartRecovery318 OpenModuleGluedSheaf318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
  {M N P : ι → X.Modules}

/-- A morphism of the original local module data, on every actual subopen.
Its only compatibility condition is the original transition square. -/
structure Map (D : Data U M) (E : Data U N) where
  app : ∀ i (W : X.Opens), W ≤ U i → Γ(M i,W) →ₗ[Γ(X,W)] Γ(N i,W)
  natural : ∀ i (W V : X.Opens) (hi : W ≤ U i) (h : V ≤ W) (s : Γ(M i,W)),
    res (N i) h (app i W hi s) = app i V (h.trans hi) (res (M i) h s)
  compatible : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (s : Γ(M i,W)),
    E.transition i j W hi hj (app i W hi s) = app j W hj (D.transition i j W hi hj s)

variable {D : Data U M} {E : Data U N} {F : Data U P}

@[ext] lemma Map.ext {f g : Map D E} (h : ∀ i W hi s, f.app i W hi s = g.app i W hi s) : f = g := by
  cases f with | mk f fn fc =>
    cases g with | mk g gn gc =>
      have he : f = g := by funext i W hi; exact LinearMap.ext (h i W hi)
      subst g
      rfl

@[expose] def identity (D : Data U M) : Map D D where
  app _ _ _ := LinearMap.id
  natural _ _ _ _ _ _ := rfl
  compatible _ _ _ _ _ _ := rfl

@[expose] def compose (f : Map D E) (g : Map E F) : Map D F where
  app i W hi := (g.app i W hi).comp (f.app i W hi)
  natural i W V hi h s := by
    change res (P i) h (g.app i W hi (f.app i W hi s)) = _
    rw [g.natural, f.natural]
    rfl
  compatible i j W hi hj s := by
    change F.transition i j W hi hj (g.app i W hi (f.app i W hi s)) = _
    rw [g.compatible, f.compatible]
    rfl

/-- Apply the given original chart maps to the actual matching family. -/
@[expose] def sectionMap (f : Map D E) (W : X.Opens) (s : sections D W) : sections E W :=
  ⟨fun i => f.app i (W ⊓ U i) inf_le_right (s.val i), by
    intro i j V hW hi hj
    rw [f.natural, f.natural, f.compatible, s.property i j V hW hi hj]⟩

lemma sectionMap_add (f : Map D E) (W : X.Opens) (s t : sections D W) :
    sectionMap f W (s + t) = sectionMap f W s + sectionMap f W t := by
  apply Subtype.ext
  funext i
  exact map_add _ _ _

lemma sectionMap_smul (f : Map D E) (W : X.Opens) (a : Γ(X,W)) (s : sections D W) :
    sectionMap f W (a • s) = a • sectionMap f W s := by
  apply Subtype.ext
  funext i
  exact map_smul (f.app i (W ⊓ U i) inf_le_right)
    (X.presheaf.map (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op a) (s.val i)

lemma sectionMap_restrict (f : Map D E) {W V : X.Opens} (h : V ≤ W) (s : sections D W) :
    restrict E h (sectionMap f W s) = sectionMap f V (restrict D h s) := by
  apply Subtype.ext
  funext i
  exact f.natural i (W ⊓ U i) (V ⊓ U i) inf_le_right (inf_le_inf_right (U i) h) (s.val i)

/-- The constructed map is an actual morphism of module sheaves on X. -/
@[expose] def sheafMap (f : Map D E) : sheaf D ⟶ sheaf E where
  val :=
    { app := fun W => ModuleCat.ofHom
        { toFun := sectionMap f W.unop
          map_add' := sectionMap_add f W.unop
          map_smul' := sectionMap_smul f W.unop }
      naturality := by
        intro W V h
        ext s
        exact (sectionMap_restrict f (leOfHom h.unop) s).symm }

/-- The map recovers the input on each original chart and every subopen. -/
lemma evaluate_sheafMap (f : Map D E) (i : ι) (W : X.Opens) (hi : W ≤ U i)
    (s : sections D W) :
    evaluate E i W hi ((sheafMap f).val.app (op W) s) = f.app i W hi (evaluate D i W hi s) := by
  exact f.natural i (W ⊓ U i) W inf_le_right (le_inf le_rfl hi) (s.val i)

lemma sheafMap_identity (D : Data U M) : sheafMap (identity D) = 𝟙 (sheaf D) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  rfl

lemma sheafMap_compose (f : Map D E) (g : Map E F) :
    sheafMap (compose f g) = sheafMap f ≫ sheafMap g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext s
  rfl
end OpenModuleDescentMaps318
