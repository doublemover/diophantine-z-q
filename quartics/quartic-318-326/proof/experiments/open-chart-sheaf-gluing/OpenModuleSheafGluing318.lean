module
public import OpenModulePresheaf318
public section
noncomputable section
namespace OpenModuleSheafGluing318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace ModuleLocalGluing318
open OpenModuleTransition318 OpenModuleChartRecovery318 OpenModulePresheaf318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : Data U M)
variable {κ : Type u} (V : κ → X.Opens) (W : X.Opens)
  (hV : ∀ k, V k ≤ W) (hcover : W ≤ iSup V)
  (s : ∀ k, D.sections (V k))
  (hs : ∀ k l (Z : X.Opens) (hk : Z ≤ V k) (hl : Z ≤ V l),
    D.restrict hk (s k) = D.restrict hl (s l))

include hcover in
lemma component_cover (i : ι) : W ⊓ U i ≤ iSup (fun k => V k ⊓ U i) := by
  intro x hx
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcover hx.1)
  exact Opens.mem_iSup.mpr ⟨k, hk, hx.2⟩

lemma component_compatible (i : ι) :
    TopCat.Presheaf.IsCompatible (M i).presheaf (fun k => V k ⊓ U i)
      (fun k => (s k).val i) := by
  intro k l
  let Z := (V k ⊓ U i) ⊓ (V l ⊓ U i)
  have hZi : Z ≤ U i := inf_le_left.trans inf_le_right
  have hh := congrArg (evaluate D i Z hZi)
    (hs k l Z (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  simpa only [evaluate_restrict] using hh

/-- Glue each original local sheaf component using its actual sheaf law. -/
@[expose] def gluedComponent (i : ι) : Γ(M i,W ⊓ U i) :=
  Classical.choose (TopCat.Sheaf.existsUnique_gluing'
    (⟨(M i).presheaf,(M i).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun k => V k ⊓ U i) (W ⊓ U i)
    (fun k => homOfLE (inf_le_inf_right (U i) (hV k)))
    (component_cover V W hcover i) (fun k => (s k).val i)
    (component_compatible D V s hs i))

lemma gluedComponent_restrict (i : ι) (k : κ) :
    res (M i) (inf_le_inf_right (U i) (hV k))
      (gluedComponent D V W hV hcover s hs i) = (s k).val i :=
  (Classical.choose_spec (TopCat.Sheaf.existsUnique_gluing'
    (⟨(M i).presheaf,(M i).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun k => V k ⊓ U i) (W ⊓ U i)
    (fun k => homOfLE (inf_le_inf_right (U i) (hV k)))
    (component_cover V W hcover i) (fun k => (s k).val i)
    (component_compatible D V s hs i))).1 k

lemma gluedComponent_subopen (i : ι) (k : κ) (Z : X.Opens)
    (hk : Z ≤ V k) (hi : Z ≤ U i) :
    res (M i) (le_inf (hk.trans (hV k)) hi) (gluedComponent D V W hV hcover s hs i) =
      res (M i) (le_inf hk hi) ((s k).val i) := by
  have h := congrArg (res (M i) (le_inf hk hi))
    (gluedComponent_restrict D V W hV hcover s hs i k)
  simpa only [res_res] using h

/-- Componentwise gluing preserves every original overlap transition. -/
lemma glued_compatible : D.Compatible W (gluedComponent D V W hV hcover s hs) := by
  intro i j Z hZ hi hj
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(M j).presheaf,(M j).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun k => Z ⊓ V k) Z (fun _ => homOfLE inf_le_left)
    (by
      intro x hx
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcover (hZ hx))
      exact Opens.mem_iSup.mpr ⟨k, hx, hk⟩)
  intro k
  change res (M j) inf_le_left
      (D.transition i j Z hi hj (res (M i) (le_inf hZ hi)
        (gluedComponent D V W hV hcover s hs i))) =
    res (M j) inf_le_left (res (M j) (le_inf hZ hj)
      (gluedComponent D V W hV hcover s hs j))
  rw [D.natural, res_res, res_res]
  rw [gluedComponent_subopen D V W hV hcover s hs i k (Z ⊓ V k)
    inf_le_right (inf_le_left.trans hi)]
  rw [gluedComponent_subopen D V W hV hcover s hs j k (Z ⊓ V k)
    inf_le_right (inf_le_left.trans hj)]
  exact (s k).property i j (Z ⊓ V k) inf_le_right
    (inf_le_left.trans hi) (inf_le_left.trans hj)

/-- The global matching family is an actual section, not merely its
componentwise existence or an assumed sheafification. -/
@[expose] def glued : D.sections W :=
  ⟨gluedComponent D V W hV hcover s hs, glued_compatible D V W hV hcover s hs⟩

lemma glued_restrict (k : κ) : D.restrict (hV k) (glued D V W hV hcover s hs) = s k := by
  apply Subtype.ext
  funext i
  exact gluedComponent_restrict D V W hV hcover s hs i k

lemma glued_unique (t : D.sections W) (ht : ∀ k, D.restrict (hV k) t = s k) :
    t = glued D V W hV hcover s hs := by
  apply Subtype.ext
  funext i
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(M i).presheaf,(M i).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun k => V k ⊓ U i) (W ⊓ U i)
    (fun k => homOfLE (inf_le_inf_right (U i) (hV k))) (component_cover V W hcover i)
  intro k
  change res (M i) (inf_le_inf_right (U i) (hV k)) (t.val i) =
    res (M i) (inf_le_inf_right (U i) (hV k)) (gluedComponent D V W hV hcover s hs i)
  rw [gluedComponent_restrict]
  exact congrArg (fun z : D.sections (V k) => z.val i) (ht k)
end OpenModuleSheafGluing318
