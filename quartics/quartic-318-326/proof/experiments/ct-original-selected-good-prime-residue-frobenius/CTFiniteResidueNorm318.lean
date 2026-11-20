module
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public section
noncomputable section

namespace CTFiniteResidueNorm318

private theorem geom_nat (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    (q-1)*(∑ i ∈ Finset.range n, q^i) + 1 = q^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,add_right_comm,ih]
    rw [add_comm (q^n),← Nat.succ_mul,Nat.sub_add_cancel hq,pow_succ,mul_comm]

/-- Actual norm on the multiplicative units of a finite residue extension.
The generator calculation is valid even when the field characteristic
divides the extension degree. -/
theorem finite_field_unit_norm_surj (k l : Type*) [Field k] [Field l]
    [Fintype k] [Fintype l] [Algebra k l] :
    Function.Surjective (Units.map (Algebra.norm k : l →* k)) := by
  classical
  let N := Units.map (Algebra.norm k : l →* k)
  let j := Units.map (algebraMap k l).toMonoidHom
  have hj : Function.Injective j := Units.map_injective (algebraMap k l).injective
  let q := Nat.card k
  let n := Module.finrank k l
  let E := ∑ i ∈ Finset.range n, q^i
  have hq : 1 ≤ q := Nat.card_pos
  have hl : Nat.card l = q^n := by
    dsimp [q,n]
    simpa only [Nat.card_eq_fintype_card] using (Module.card_eq_pow_finrank (K := k) (V := l))
  have hU : Nat.card lˣ = Nat.card kˣ * E := by
    rw [Nat.card_units,Nat.card_units,hl]
    change q^n-1 = (q-1)*E
    rw [← geom_nat q hq n,Nat.add_sub_cancel]
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := lˣ)
  have hOrd := orderOf_eq_card_of_forall_mem_zpowers hg
  have hE : E ≠ 0 := by
    intro he
    have hh : 0 < Nat.card lˣ := Nat.card_pos
    rw [hU,he,mul_zero] at hh
    exact (Nat.lt_irrefl _ hh)
  have hdiv : E ∣ orderOf g := by
    rw [hOrd,hU,mul_comm]
    exact dvd_mul_right _ _
  have he : j (N g) = g^E := by
    apply Units.ext
    change algebraMap k l (Algebra.norm k (g : l)) = ((g^E : lˣ) : l)
    rw [FiniteField.algebraMap_norm_eq_pow_sum]
    exact ((Units.coeHom l).map_pow g E).symm
  have hGen : orderOf (N g) = Nat.card kˣ := by
    rw [← orderOf_injective j hj (N g),he,orderOf_pow_of_dvd hE hdiv,hOrd,hU]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hE)
  have htop : Subgroup.zpowers (N g) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top,Nat.card_zpowers,hGen]
  intro a
  have ha : a ∈ Subgroup.zpowers (N g) := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨m,hm⟩ := ha
  exact ⟨g^m, (map_zpow N g m).trans hm⟩

end CTFiniteResidueNorm318
