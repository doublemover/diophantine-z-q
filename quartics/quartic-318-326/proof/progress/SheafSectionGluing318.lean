module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Tactic
public section
noncomputable section
universe u
namespace SheafSectionGluing318
open CategoryTheory Opposite TopologicalSpace TopCat TopCat.Presheaf
set_option maxHeartbeats 0
variable {X : TopCat.{u}} (S : TopCat.Sheaf RingCat.{u} X)
  (M : SheafOfModules.{u} S) {ι : Type u} (U : ι → Opens X)

/-- Use the actual sheaf-of-modules structure, not a parallel section object. -/
theorem module_unique_gluing (hcover : (⊤ : Opens X) ≤ iSup U)
    (sf : ∀ i, M.val.obj (op (U i)))
    (hcompat : TopCat.Presheaf.IsCompatible M.val.presheaf U sf) :
    ∃! s : M.val.obj (op (⊤ : Opens X)),
      ∀ i, M.val.map (homOfLE (show U i ≤ ⊤ from le_top)).op s = sf i := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  exact F.existsUnique_gluing' U ⊤
    (fun i => homOfLE le_top) hcover sf hcompat

/-- An element over the top open gives a genuine global section of the
actual sheaf of modules, with all its naturality equations. -/
def fromTop (s : M.val.obj (op (⊤ : Opens X))) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s) (by
      intro V W f
      rw [←PresheafOfModules.map_comp_apply]
      congr 1)

/-- Unique gluing into Mathlib's actual global module-section type. -/
theorem global_unique_gluing (hcover : (⊤ : Opens X) ≤ iSup U)
    (sf : ∀ i, M.val.obj (op (U i)))
    (hcompat : TopCat.Presheaf.IsCompatible M.val.presheaf U sf) :
    ∃! s : M.sections, ∀ i, s.val (op (U i)) = sf i := by
  obtain ⟨s,hs,huniq⟩ := module_unique_gluing S M U hcover sf hcompat
  refine ⟨fromTop S M s,hs,?_⟩
  intro s' hs'
  have ht : s'.val (op (⊤ : Opens X)) = s := by
    apply huniq
    intro i
    rw [PresheafOfModules.sections_property]
    exact hs' i
  apply PresheafOfModules.sections_ext
  intro V
  change s'.val V = M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s
  rw [←ht,PresheafOfModules.sections_property]

/-- Two actual global module sections from local rank-one frames and the
quadratic coefficient transition. Compatibility of module sections is derived
from the frame identities; it is not supplied as the gluing premise. -/
theorem pair_from_quadratic_frames (hcover : (⊤ : Opens X) ≤ iSup U)
    (frame : ∀ i, (S.obj.obj (op (U i))) ≃ₗ[S.obj.obj (op (U i))] M.val.obj (op (U i)))
    (overlap : ∀ i j, (S.obj.obj (op (U i ⊓ U j))) ≃ₗ[S.obj.obj (op (U i ⊓ U j))]
      M.val.obj (op (U i ⊓ U j)))
    (unit : ∀ i j, (S.obj.obj (op (U i ⊓ U j)))ˣ)
    (left_frame : ∀ i j a,
      M.val.map (Opens.infLELeft (U i) (U j)).op (frame i a) =
      overlap i j (S.obj.map (Opens.infLELeft (U i) (U j)).op a))
    (right_frame : ∀ i j a,
      M.val.map (Opens.infLERight (U i) (U j)).op (frame j a) =
      overlap i j ((↑((unit i j)^2)⁻¹) *
        S.obj.map (Opens.infLERight (U i) (U j)).op a))
    (a : Fin 2 → ∀ i, S.obj.obj (op (U i)))
    (transition : ∀ k i j,
      S.obj.map (Opens.infLERight (U i) (U j)).op (a k j) =
      ↑((unit i j)^2) * S.obj.map (Opens.infLELeft (U i) (U j)).op (a k i)) :
    ∃! s : Fin 2 → M.sections,
      ∀ k i, (s k).val (op (U i)) = frame i (a k i) := by
  have hc (k : Fin 2) : TopCat.Presheaf.IsCompatible M.val.presheaf U
      (fun i => frame i (a k i)) := by
    intro i j
    change M.val.map (Opens.infLELeft (U i) (U j)).op (frame i (a k i)) =
      M.val.map (Opens.infLERight (U i) (U j)).op (frame j (a k j))
    rw [left_frame,right_frame,transition]
    congr 1
    exact (Units.inv_mul_cancel_left ((unit i j)^2) _).symm
  have he (k : Fin 2) := global_unique_gluing S M U hcover (fun i => frame i (a k i)) (hc k)
  choose s hs huniq using he
  refine ⟨s,hs,?_⟩
  intro s' hs'
  funext k
  exact huniq k (s' k) (hs' k)

end SheafSectionGluing318
