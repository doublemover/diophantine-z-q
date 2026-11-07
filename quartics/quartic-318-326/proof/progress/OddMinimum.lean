module
public import Height13RealLog
public import Mathlib.Order.Filter.Ultrafilter.Basic
public section
open Filter
namespace OddMinimum
variable {Stage Param : Type*}

/-- A bounded-weight visible depth on one ultrafilter-large set. -/
def Attained (F : Ultrafilter Stage) (weight : Param → ℕ)
    (visible : Stage → Param → Prop) (depth : Stage → Param → ℤ) (r : ℤ) : Prop :=
  ∃ W : ℕ, ∀ᶠ s in (F : Filter Stage),
    ∃ D, visible s D ∧ weight D ≤ W ∧ depth s D = r

/-- The odd minimum exists only after a global coarse lower bound and a
    persistent bounded-weight witness have supplied these two hypotheses. -/
theorem exists_attained_minimum (F : Ultrafilter Stage) (weight : Param → ℕ)
    (visible : Stage → Param → Prop) (depth : Stage → Param → ℤ) (C : ℤ)
    (hcoarse : ∀ s D, visible s D → C ≤ depth s D)
    (hwitness : ∃ r, Attained F weight visible depth r) :
    ∃ delta, Attained F weight visible depth delta ∧
      ∀ r, Attained F weight visible depth r → delta ≤ r := by
  apply Int.exists_least_of_bdd _ hwitness
  refine ⟨C, ?_⟩
  rintro r ⟨W, hr⟩
  obtain ⟨s,D,hvis,_,hd⟩ := hr.exists
  simpa [hd] using hcoarse s D hvis

/-- The quantifier switch in F.6: at every fixed weight budget, one large
    set of stages works for ALL visible parameters, not a chosen sequence. -/
theorem simultaneous_bounded_depth (F : Ultrafilter Stage) (weight : Param → ℕ)
    (visible : Stage → Param → Prop) (depth : Stage → Param → ℤ) (C delta : ℤ)
    (hcoarse : ∀ s D, visible s D → C ≤ depth s D)
    (hminimum : ∀ r, Attained F weight visible depth r → delta ≤ r) (W : ℕ) :
    ∀ᶠ s in (F : Filter Stage),
      ∀ D, visible s D → weight D ≤ W → delta ≤ depth s D := by
  classical
  by_contra hbad
  have hbad' := Ultrafilter.eventually_not.mpr hbad
  have hsmall : ∀ᶠ s in (F : Filter Stage),
      ∃ r ∈ Set.Icc C (delta-1),
        ∃ D, visible s D ∧ weight D ≤ W ∧ depth s D = r := by
    filter_upwards [hbad'] with s hs
    push Not at hs
    obtain ⟨D,hvis,hw,hd⟩ := hs
    refine ⟨depth s D, ⟨hcoarse s D hvis, ?_⟩, D, hvis, hw, rfl⟩
    omega
  obtain ⟨r,hr,hevent⟩ :=
    (Ultrafilter.eventually_exists_mem_iff (Set.finite_Icc C (delta-1))).mp hsmall
  have hmin := hminimum r ⟨W,hevent⟩
  have hupper := hr.2
  omega

/-- Finite symbol tables can be selected on the SAME ultrafilter. -/
theorem finite_table_stabilizes {Table : Type*} [Finite Table]
    (F : Ultrafilter Stage) (table : Stage → Table) :
    ∃ chosen, ∀ᶠ s in (F : Filter Stage), table s = chosen := by
  apply Ultrafilter.eventually_exists_iff.mp
  exact Filter.Eventually.of_forall (fun s => ⟨table s, rfl⟩)

/-- Chosen tables at different budgets have compatible restrictions by a
    finite intersection, with no stage asserted to serve all budgets. -/
theorem stabilized_restriction {Small Big : Type*} (F : Ultrafilter Stage)
    (small : Stage → Small) (big : Stage → Big) (restrict : Big → Small)
    (s0 : Small) (b0 : Big)
    (hs : ∀ᶠ s in (F : Filter Stage), small s = s0)
    (hb : ∀ᶠ s in (F : Filter Stage), big s = b0)
    (hc : ∀ᶠ s in (F : Filter Stage), restrict (big s) = small s) :
    restrict b0 = s0 := by
  obtain ⟨s,hsmall,hbig,hcompat⟩ := (hs.and (hb.and hc)).exists
  simpa [hsmall,hbig] using hcompat

/-- Every finite test valid on a large set survives in its stabilized table. -/
theorem stabilized_property {Table : Type*} (F : Ultrafilter Stage)
    (table : Stage → Table) (chosen : Table) (P : Table → Prop)
    (hc : ∀ᶠ s in (F : Filter Stage), table s = chosen)
    (hp : ∀ᶠ s in (F : Filter Stage), P (table s)) : P chosen := by
  obtain ⟨s,hs,hPs⟩ := (hc.and hp).exists
  simpa [hs] using hPs

#print axioms exists_attained_minimum
#print axioms simultaneous_bounded_depth
#print axioms finite_table_stabilizes
#print axioms stabilized_restriction
#print axioms stabilized_property
end OddMinimum
