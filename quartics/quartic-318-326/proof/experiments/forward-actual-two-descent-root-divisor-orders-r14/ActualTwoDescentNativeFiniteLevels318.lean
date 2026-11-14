module
public import ActualTwoDescentNativeInverseLimitTopology318
public section
noncomputable section
namespace ActualTwoDescentNativeFiniteLevels318
open ActualTwoDescentActualPrimarySelmer318 ActualTwoDescentAdditivePrimaryLevels318
open ActualTwoDescentPrueferLevelCoordinates318 ActualTwoDescentNativeLevelRestriction318
open ActualTwoDescentFullPrimarySelmerPruefer318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentActualShaReducedDuality318

/-- Restrict the actual global equivalence to the ACTUAL killed subgroup.
The exponent is unchanged in both directions. -/
def actualSelmerLevelPrueferEquiv (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (k : ℕ) :
    additivePowerLevel (actualPrimarySelmer n hn) k ≃+ PrueferLevel k where
  toFun x := ⟨e x.val,by change (2^k) • e x.val=0; rw [←map_nsmul,x.property,map_zero]⟩
  invFun x := ⟨e.symm x.val,by change (2^k) • e.symm x.val=0; rw [←map_nsmul,x.property,map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)

def actualSelmerLevelCoordinate (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (k : ℕ) :
    additivePowerLevel (actualPrimarySelmer n hn) k ≃+ ZMod (2^k) :=
  (actualSelmerLevelPrueferEquiv n hn e k).trans (prueferLevelCoordinate k).symm

lemma actual_native_level_finite_of_equiv (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (k : ℕ) :
    Finite (DiscreteSelmerLevel n hn k) := by
  letI := actual_pruefer_level_finite k
  haveI := Finite.of_equiv (PrueferLevel k) (actualSelmerLevelPrueferEquiv n hn e k).symm.toEquiv
  exact inferInstanceAs (Finite (Multiplicative (additivePowerLevel (actualPrimarySelmer n hn) k)))

lemma actual_native_level_card_of_equiv (n : ℚ) (hn : n ≠ 0)
    (e : actualPrimarySelmer n hn ≃+ PrueferAdd) (k : ℕ) :
    Nat.card (DiscreteSelmerLevel n hn k)=2^k := by
  change Nat.card (Multiplicative (additivePowerLevel (actualPrimarySelmer n hn) k))=2^k
  change Nat.card (additivePowerLevel (actualPrimarySelmer n hn) k)=2^k
  rw [Nat.card_congr (actualSelmerLevelPrueferEquiv n hn e k).toEquiv]
  exact actual_pruefer_level_card k

/-- Under the retained genuine global reduced-duality hypothesis, each
original level has exactly 2^k elements and its NATIVE dual is finite.
The preceding inverse-limit homeomorphism itself needs none of these hypotheses. -/
theorem actual_native_levels_finite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn)
    (k : ℕ) :
    Nat.card (DiscreteSelmerLevel n hn k)=2^k ∧ Finite (NativeLevelDual n hn k) := by
  obtain ⟨e⟩ := actual_full_primary_selmer_pruefer n hn hf hb hS hdual
  letI := actual_native_level_finite_of_equiv n hn e k
  exact ⟨actual_native_level_card_of_equiv n hn e k,inferInstance⟩

end ActualTwoDescentNativeFiniteLevels318
