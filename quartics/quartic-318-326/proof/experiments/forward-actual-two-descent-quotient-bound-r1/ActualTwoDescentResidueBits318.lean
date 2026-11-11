module
public import ActualTwoDescentFreshPrime318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public section
noncomputable section
namespace ActualTwoDescentResidueBits318
open FixedSquarefreeCRT318
set_option maxHeartbeats 16000000

@[expose] def bitSign (b : Bool) : ℤ := if b then -1 else 1

/-- Every desired Legendre bit is realized by an actual NONZERO residue
unit of the original prime field, before any prime progression is chosen. -/
theorem actual_bit_unit (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (b : Bool) :
    ∃ u : (ZMod p)ˣ, quadraticChar (ZMod p) (u : ZMod p)=bitSign b := by
  cases b with
  | false => exact ⟨1,by simp [bitSign]⟩
  | true =>
    exact quadraticChar_exists_neg_one'
      (by simpa only [ringChar_zmod_n] using hp2 : ringChar (ZMod p) ≠ 2)

/-- The ACTUAL finite-support CRT equivalence merges all selected unit
residues. The empty support is allowed and has modulus1. -/
def supportUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (u : ∀ i, (ZMod (p i))ˣ) : (ZMod (modulus p))ˣ := by
  let uv : (∀ i, ZMod (p i))ˣ :=
    { val := fun i => u i
      inv := fun i => ↑((u i)⁻¹)
      val_inv := by funext i; simp
      inv_val := by funext i; simp }
  exact Units.map (ringEquiv p hp hd).symm.toMonoidHom uv

lemma actual_support_unit_component {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (u : ∀ i, (ZMod (p i))ˣ) (i : ι) :
    component p i (supportUnit p hp hd u : ZMod (modulus p))=u i := by
  change (ringEquiv p hp hd ((ringEquiv p hp hd).symm (fun j => (u j : ZMod (p j))))) i = _
  rw [RingEquiv.apply_symm_apply]

end ActualTwoDescentResidueBits318
