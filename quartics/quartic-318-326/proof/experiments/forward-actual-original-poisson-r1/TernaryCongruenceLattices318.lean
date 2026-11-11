module
public import TernaryQuadraticLineCover318
public import Mathlib.GroupTheory.Index
public section
noncomputable section
namespace TernaryCongruenceLattices318
open TernaryQuadraticLineCover318
set_option maxHeartbeats 1000000

@[expose] def reduce (p : ℕ) : Vector ℤ →+ Vector (ZMod p) where
  toFun v := ((v.1:ZMod p),(v.2.1:ZMod p),(v.2.2:ZMod p))
  map_zero' := by simp
  map_add' v w := by simp

lemma reduce_surjective (p : ℕ) [NeZero p] : Function.Surjective (reduce p) := by
  rintro ⟨x,z,w⟩
  refine ⟨((x.val:ℤ),(z.val:ℤ),(w.val:ℤ)),?_⟩
  change (((x.val:ℤ):ZMod p),((z.val:ℤ):ZMod p),((w.val:ℤ):ZMod p))=(x,z,w)
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

@[expose] def integerCode (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p)) :
    Vector ℤ →+ (ZMod p×ZMod p) :=
  (lineCode (κ : ZMod p) t).comp (reduce p)

lemma integer_code_surjective (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p)) :
    Function.Surjective (integerCode p κ t) :=
  (code_surjective (κ : ZMod p) t).comp (reduce_surjective p)

/-- These are the actual additive congruence lattices in the original
integer coordinates (x,z,w), not abstract finite subspaces. -/
@[expose] def lattice (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p)) :
    AddSubgroup (Vector ℤ) := (integerCode p κ t).ker

/-- Exact covolume index p² from a constructed surjective residue code. -/
theorem lattice_index (p : ℕ) [Fact p.Prime] (κ : ℤ) (t : Option (ZMod p)) :
    (lattice p κ t).index=p^2 := by
  rw [lattice,AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (integerCode p κ t)
      (integer_code_surjective p κ t)).toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card,pow_two]

/-- Exact original ternary divisibility, with no chosen projective point. -/
theorem divisor_iff_lattice (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (κ : ℤ)
    (hκ : ¬(p:ℤ)∣κ) (v : Vector ℤ) :
    (p:ℤ)∣κ*v.2.2^2-2*v.1*v.2.1 ↔ ∃ t : Option (ZMod p), v∈lattice p κ t := by
  have hk : (κ : ZMod p)≠0 := by
    intro he
    exact hκ ((ZMod.intCast_zmod_eq_zero_iff_dvd κ p).mp he)
  have heq : (p:ℤ)∣κ*v.2.2^2-2*v.1*v.2.1 ↔ equation (κ : ZMod p) (reduce p v) := by
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [equation,reduce,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_sub,
      Int.cast_mul,Int.cast_pow,Int.cast_ofNat,sub_eq_zero,eq_comm]
  rw [heq,equation_iff_code (κ : ZMod p) hk (GoodReductionResidue318.two_residue_ne p hp2)]
  rfl

/-- There are exactly p+1 indexed congruence lattices in this constructed
cover. Distinctness is not needed for the later upper bound. -/
theorem lattice_parameter_card (p : ℕ) [Fact p.Prime] :
    Fintype.card (Option (ZMod p))=p+1 := by simp only [Fintype.card_option,ZMod.card]

end TernaryCongruenceLattices318
