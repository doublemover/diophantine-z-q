module

public import SelectedSameASignedLiftCocycle318
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Given the exact signed coboundary of the actual local lift cocycle,
construct a global lift on the literal top open and prove its actual
derived boundary vanishes. No arbitrary Cech comparison is used.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameACoboundaryGivesActualGlobalLift318

universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SelectedSameAActualLiftDifference318 (Sh)
open SelectedSameASignedLiftCocycle318

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable (S : ShortComplex (Sh X)) (hS : S.ShortExact)
variable {ι : Type u} (U : ι → Opens X) (hU : (⊤ : Opens X) ≤ ⨆ i, U i)
variable (z : S.X₃.obj.obj (op (⊤ : Opens X)))
variable (t : ∀ i, S.X₂.obj.obj (op (U i)))
variable (ht : ∀ i, S.g.hom.app (op (U i)) (t i) = res X S.X₃ le_top z)

variable (c : ∀ i, S.X₁.obj.obj (op (U i)))
variable (hc : ∀ i j, coeff X S hS U z t ht i j =
  res X S.X₁ inf_le_left (c i) - res X S.X₁ inf_le_right (c j))

include hS hU ht hc

/-- Actual cochain correction and sheaf gluing, without assuming a
global cohomology equivalence. The difference sign is fixed. -/
theorem globalLift :
    ∃ q : S.X₂.obj.obj (op (⊤ : Opens X)), S.g.hom.app (op (⊤ : Opens X)) q = z := by
  let w (i : ι) : S.X₂.obj.obj (op (U i)) := t i + S.f.hom.app (op (U i)) (c i)
  have hPair : TopCat.Presheaf.IsCompatible S.X₂.obj U w := by
    intro i j
    change res X S.X₂ inf_le_left (w i) = res X S.X₂ inf_le_right (w j)
    unfold w
    rw [map_add, map_add, ← res_natural X, ← res_natural X]
    have e := coeff_beta X S hS U z t ht i j
    rw [hc, map_sub] at e
    apply sub_eq_zero.mp
    calc
      _ = (res X S.X₂ inf_le_left (t i) - res X S.X₂ inf_le_right (t j)) +
          (S.f.hom.app (op (U i ⊓ U j)) (res X S.X₁ inf_le_left (c i)) -
            S.f.hom.app (op (U i ⊓ U j)) (res X S.X₁ inf_le_right (c j))) := by abel
      _ = (res X S.X₂ inf_le_left (t i) - res X S.X₂ inf_le_right (t j)) +
          (res X S.X₂ inf_le_right (t j) - res X S.X₂ inf_le_left (t i)) := by rw [e]
      _ = 0 := by abel
  obtain ⟨q, hq, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₂ U ⊤
    (fun _ => homOfLE le_top) hU w hPair
  refine ⟨q, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ U ⊤ (fun _ => homOfLE le_top) hU
  intro i
  change res X S.X₃ (show U i ≤ ⊤ from le_top) (S.g.hom.app (op (⊤ : Opens X)) q) =
    res X S.X₃ le_top z
  rw [← res_natural X]
  have hqi : res X S.X₂ (show U i ≤ ⊤ from le_top) q = w i := hq i
  rw [hqi]
  change S.g.hom.app (op (U i)) (t i + S.f.hom.app (op (U i)) (c i)) = _
  have ez := congrArg (fun m : S.X₁ ⟶ S.X₃ => m.hom.app (op (U i)) (c i)) S.zero
  have e0 : S.g.hom.app (op (U i)) (S.f.hom.app (op (U i)) (c i)) = 0 := ez
  rw [map_add, ht, e0, add_zero]

variable [HasExt.{w} (Sh X)]

/-- Close the existing actual H0 boundary, with no abstract class
identification. A true global lift is in the kernel by Ext composition
with the short exact class, using the actual right arrow. -/
theorem boundary_zero :
    Sheaf.H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm z) = 0 := by
  obtain ⟨q, hq⟩ := globalLift X S hS U hU z t ht c hc
  have e := Sheaf.H.equiv₀_symm_naturality isTerminalTop S.g q
  rw [hq] at e
  change ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm z).comp hS.extClass (zero_add 1) = 0
  rw [← e, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

end SelectedSameACoboundaryGivesActualGlobalLift318
