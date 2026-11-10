module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public section
noncomputable section
namespace ExtFiniteRetractVanishing318
open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An actual finite identity decomposition through acyclic objects forces
vanishing of the original Ext group, on its unchanged carrier. -/
lemma eq_zero {X M : C} {ι : Type*} [Fintype ι] (N : ι → C)
    (out : ∀ i, M ⟶ N i) (back : ∀ i, N i ⟶ M)
    (total : ∑ i, out i ≫ back i = 𝟙 M) (n : ℕ)
    (h : ∀ i, ∀ y : Ext X (N i) n, y = 0) (x : Ext X M n) : x = 0 := by
  calc
    x = x.comp (Ext.mk₀ (𝟙 M)) (add_zero n) := (Ext.comp_mk₀_id x).symm
    _ = x.comp (Ext.mk₀ (∑ i, out i ≫ back i)) (add_zero n) := by rw [total]
    _ = ∑ i, (x.comp (Ext.mk₀ (out i)) (add_zero n)).comp
        (Ext.mk₀ (back i)) (add_zero n) := by
      simp only [Ext.mk₀_sum,Ext.comp_sum,← Ext.mk₀_comp_mk₀,
        ← Ext.comp_assoc_of_third_deg_zero]
    _ = 0 := by simp only [h,Ext.zero_comp,Finset.sum_const_zero]
end ExtFiniteRetractVanishing318
