module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Data.Fintype.EquivFin
public section
noncomputable section
namespace MonicComplexRootEnumeration318
open Polynomial

/-- Enumerate the ENTIRE root multiset, not merely its distinct values.
Multiplicity is represented by the extra finite index of each root. -/
theorem exists_roots (Q : Polynomial ℂ) (hm : Q.Monic) (m : ℕ)
    (hdeg : Q.natDegree=m) :
    ∃ r : Fin m → ℂ, Q=∏ i : Fin m, (X-C (r i)) ∧ ∀ i, Q.IsRoot (r i) := by
  classical
  let T := Q.roots.toEnumFinset
  have hcard : T.card=m := by
    rw [Multiset.card_toEnumFinset,Polynomial.card_roots_eq_natDegree,hdeg]
  let e : T ≃ Fin m := Finset.equivFinOfCardEq hcard
  let r : Fin m → ℂ := fun i => (e.symm i).val.1
  refine ⟨r,?_,?_⟩
  · have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
      (Polynomial.card_roots_eq_natDegree (p := Q))
    rw [Multiset.prod_map_eq_prod_toEnumFinset] at hprod
    calc
      Q = ∏ i ∈ T, (X-C i.1) := hprod.symm
      _ = ∏ i : T, (X-C i.val.1) := (T.prod_coe_sort _).symm
      _ = ∏ i : Fin m, (X-C (r i)) :=
        Fintype.prod_equiv e _ _ (fun i => by simp only [r,e.symm_apply_apply])
  · intro i
    apply (Polynomial.mem_roots hm.ne_zero).mp
    exact Multiset.mem_of_mem_toEnumFinset (e.symm i).property
end MonicComplexRootEnumeration318
