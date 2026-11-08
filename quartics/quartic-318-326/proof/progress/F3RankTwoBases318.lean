module
public import F3NineDimension318
public import F3PairIndependence318
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public section
noncomputable section
namespace F3RankTwoBases318
variable (V : Type*) [AddCommGroup V] [Module (ZMod 3) V]
/-- These are actual ordered independent pairs in the given additive module. -/
abbrev Pairs := {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1 ∧ p.2 ≠ -p.1}
abbrev Families := {v : Fin 2 → V // LinearIndependent (ZMod 3) v}
/-- Explicit conversion between pairs and two-vector linearly independent families. -/
def pairEquiv : Pairs V ≃ Families V where
  toFun p := ⟨![p.val.1,p.val.2], (F3PairIndependence318.pair_iff _ _).mpr p.property⟩
  invFun v := ⟨(v.val 0,v.val 1), (F3PairIndependence318.pair_iff _ _).mp (by
    convert v.property using 1
    ext i
    fin_cases i <;> rfl)⟩
  left_inv p := by rfl
  right_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
/-- The inverse is the actual basis with precisely the two original vectors. -/
def familyBasisEquiv (hd : Module.finrank (ZMod 3) V = 2) :
    Families V ≃ Module.Basis (Fin 2) (ZMod 3) V where
  toFun v := basisOfLinearIndependentOfCardEqFinrank v.property (by simpa using hd.symm)
  invFun b := ⟨b,b.linearIndependent⟩
  left_inv v := by
    apply Subtype.ext
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  right_inv b := by
    apply DFunLike.coe_injective
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _

def pairBasisEquiv (hd : Module.finrank (ZMod 3) V = 2) :
    Pairs V ≃ Module.Basis (Fin 2) (ZMod 3) V :=
  (pairEquiv V).trans (familyBasisEquiv V hd)

@[simp] theorem pairBasis_zero (hd : Module.finrank (ZMod 3) V = 2) (p : Pairs V) :
    pairBasisEquiv V hd p 0 = p.val.1 := by
  simp only [pairBasisEquiv, Equiv.trans_apply, familyBasisEquiv, Equiv.coe_fn_mk,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl
@[simp] theorem pairBasis_one (hd : Module.finrank (ZMod 3) V = 2) (p : Pairs V) :
    pairBasisEquiv V hd p 1 = p.val.2 := by
  simp only [pairBasisEquiv, Equiv.trans_apply, familyBasisEquiv, Equiv.coe_fn_mk,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-- Counts the actual independent families using their dimension, not a chosen set labeling. -/
theorem card_families [Finite V] (hd : Module.finrank (ZMod 3) V = 2) :
    Nat.card (Families V) = 48 := by
  have h := card_linearIndependent (K := ZMod 3) (V := V) (k := 2) (by omega)
  simpa [Families, hd, Fin.prod_univ_two] using h

theorem card_pairs (hc : Nat.card V = 9) : Nat.card (Pairs V) = 48 := by
  letI : Finite V := F3NineDimension318.finite V hc
  rw [Nat.card_congr (pairEquiv V)]
  exact card_families V (F3NineDimension318.finrank_two V hc)

theorem card_bases (hc : Nat.card V = 9) :
    Nat.card (Module.Basis (Fin 2) (ZMod 3) V) = 48 := by
  rw [← Nat.card_congr (pairBasisEquiv V (F3NineDimension318.finrank_two V hc))]
  exact card_pairs V hc
end F3RankTwoBases318
