module

public import SelectedSameAActualLiftDifference318
public import Mathlib.Tactic.Abel

/-!
The actual local lifts of one global section give the signed additive
cocycle of their unique kernel coefficients. Diagonal and triple
identities are produced using the literal sheaf restrictions.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameASignedLiftCocycle318

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SelectedSameAActualLiftDifference318

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- Restriction in the actual sheaf on the literal subopen. -/
abbrev res (F : Sh X) {V W : Opens X} (h : W ≤ V) :
    F.obj.obj (op V) ⟶ F.obj.obj (op W) :=
  F.obj.map (homOfLE h).op

theorem res_res (F : Sh X) {W V U : Opens X}
    (h : W ≤ V) (j : V ≤ U) (x : F.obj.obj (op U)) :
    res X F h (res X F j x) = res X F (h.trans j) x := by
  change F.obj.map (homOfLE h).op (F.obj.map (homOfLE j).op x) = _
  simp only [← F.obj.map_comp_apply, ← op_comp, homOfLE_comp]

theorem res_natural {F G : Sh X} (f : F ⟶ G) {V W : Opens X} (h : W ≤ V)
    (x : F.obj.obj (op V)) :
    f.hom.app (op W) (res X F h x) = res X G h (f.hom.app (op V) x) :=
  congrArg (fun m : F.obj.obj (op V) ⟶ G.obj.obj (op W) => m x)
    (f.hom.naturality (homOfLE h).op)

variable (S : ShortComplex (Sh X)) (hS : S.ShortExact)
variable {ι : Type u} (U : ι → Opens X)
variable (z : S.X₃.obj.obj (op (⊤ : Opens X)))
variable (t : ∀ i, S.X₂.obj.obj (op (U i)))
variable (ht : ∀ i, S.g.hom.app (op (U i)) (t i) = res X S.X₃ le_top z)

include ht in
theorem lifts_equal_restriction {W : Opens X} (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    S.g.hom.app (op W) (res X S.X₂ hi (t i)) =
      S.g.hom.app (op W) (res X S.X₂ hj (t j)) := by
  rw [res_natural X, res_natural X, ht, ht, res_res X, res_res X] <;> rfl

/-- Read the genuine right-minus-left coefficient on the full
intersection. Its only choices are proof-irrelevant by uniqueness. -/
@[expose] def coeff (i j : ι) : S.X₁.obj.obj (op (U i ⊓ U j)) :=
  Classical.choose (ExistsUnique.exists (difference_unique X S hS (U i ⊓ U j)
    (res X S.X₂ inf_le_left (t i)) (res X S.X₂ inf_le_right (t j))
    (lifts_equal_restriction X S U z t ht i j inf_le_left inf_le_right)))

theorem coeff_beta (i j : ι) :
    S.f.hom.app (op (U i ⊓ U j)) (coeff X S hS U z t ht i j) =
      res X S.X₂ inf_le_right (t j) - res X S.X₂ inf_le_left (t i) :=
  Classical.choose_spec (ExistsUnique.exists (difference_unique X S hS (U i ⊓ U j)
    (res X S.X₂ inf_le_left (t i)) (res X S.X₂ inf_le_right (t j))
    (lifts_equal_restriction X S U z t ht i j inf_le_left inf_le_right)))

theorem coeff_on_subopen (i j : ι) {W : Opens X} (h : W ≤ U i ⊓ U j) :
    S.f.hom.app (op W) (res X S.X₁ h (coeff X S hS U z t ht i j)) =
      res X S.X₂ (h.trans inf_le_right) (t j) -
        res X S.X₂ (h.trans inf_le_left) (t i) := by
  rw [res_natural X, coeff_beta, map_sub, res_res X, res_res X]

theorem coeff_diagonal (i : ι) : coeff X S hS U z t ht i i = 0 := by
  apply local_inclusion_injective X S hS (U i ⊓ U i)
  rw [coeff_beta, map_zero]
  exact sub_self _

theorem coeff_triple (i j k : ι) :
    res X S.X₁ inf_le_left (coeff X S hS U z t ht i j) +
      res X S.X₁ (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (coeff X S hS U z t ht j k) =
      res X S.X₁ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (coeff X S hS U z t ht i k) := by
  apply local_inclusion_injective X S hS ((U i ⊓ U j) ⊓ U k)
  rw [map_add, coeff_on_subopen, coeff_on_subopen, coeff_on_subopen]
  abel

end SelectedSameASignedLiftCocycle318
