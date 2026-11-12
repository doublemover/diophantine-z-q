module
public import ActualTwoDescentNativeLevelRestriction318
public section
noncomputable section
namespace ActualTwoDescentNativeScalarResidues318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentSelmerPadicAction318
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentDiscreteSelmerDual318
open ActualTwoDescentPontryaginPadicModule318 ActualTwoDescentNativeLevelRestriction318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The native character scalar on an actual level is the literal residue
power; this does not depend on a choice of a Pruefer generator. -/
lemma actual_native_scalar_level_value (n : ℚ) (hn : n ≠ 0)
    (k : ℕ) (a : ℤ_[2]) (f : ActualPontryagin n hn)
    (x : DiscreteSelmerLevel n hn k) :
    nativeLevelRestriction n hn k (nativeDualScalar n hn a f) x =
      (nativeLevelRestriction n hn k f x) ^ (PadicInt.toZModPow k a).val := by
  change f (Multiplicative.ofAdd (actualSelmerPadicEnd n hn a x.toAdd.val)) =
    (f (Multiplicative.ofAdd x.toAdd.val)) ^ (PadicInt.toZModPow k a).val
  have hs := actual_primary_padic_scalar_at_level (actual_selmer_primary n hn)
    a k x.toAdd.val x.toAdd.property
  change actualSelmerPadicEnd n hn a x.toAdd.val =
    (PadicInt.toZModPow k a).val • x.toAdd.val at hs
  rw [hs]
  exact map_pow f (Multiplicative.ofAdd x.toAdd.val) _

lemma actual_native_scalars_equal_at_level (n : ℚ) (hn : n ≠ 0)
    (k : ℕ) (a b : ℤ_[2]) (hab : PadicInt.toZModPow k a=PadicInt.toZModPow k b)
    (f : ActualPontryagin n hn) :
    nativeLevelRestriction n hn k (nativeDualScalar n hn a f) =
      nativeLevelRestriction n hn k (nativeDualScalar n hn b f) := by
  apply PontryaginDual.ext
  intro x
  rw [actual_native_scalar_level_value,actual_native_scalar_level_value,hab]

lemma actual_native_scalar_annihilates_level (n : ℚ) (hn : n ≠ 0)
    (k : ℕ) (a : ℤ_[2]) (ha : PadicInt.toZModPow k a=0)
    (f : ActualPontryagin n hn) :
    nativeDualScalar n hn a f ∈ nativeLevelAnnihilator n hn k := by
  change nativeLevelRestriction n hn k (nativeDualScalar n hn a f)=1
  apply PontryaginDual.ext
  intro x
  rw [actual_native_scalar_level_value,ha]
  simp

/-- Every level annihilator is preserved by the actual native scalar. -/
lemma actual_native_annihilator_scalar_stable (n : ℚ) (hn : n ≠ 0)
    (k : ℕ) (a : ℤ_[2]) (f : ActualPontryagin n hn)
    (hf : f ∈ nativeLevelAnnihilator n hn k) :
    nativeDualScalar n hn a f ∈ nativeLevelAnnihilator n hn k := by
  change nativeLevelRestriction n hn k (nativeDualScalar n hn a f)=1
  change nativeLevelRestriction n hn k f=1 at hf
  apply PontryaginDual.ext
  intro x
  rw [actual_native_scalar_level_value,hf]
  simp

end ActualTwoDescentNativeScalarResidues318
