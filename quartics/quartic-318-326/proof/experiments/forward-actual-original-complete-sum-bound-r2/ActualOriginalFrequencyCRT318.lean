module
public import ActualOriginalLatticeFourierSummability318
public import Mathlib.Algebra.Group.Units.Equiv
public section
noncomputable section
namespace ActualOriginalFrequencyCRT318
open QuadricCRTAssembly318 ActualOriginalResidueFourierLift318
set_option maxHeartbeats 16000000

@[expose] def first (m n : ℕ) (h : m.Coprime n) : ZMod (m*n) →+* ZMod m :=
  (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom
@[expose] def second (m n : ℕ) (h : m.Coprime n) : ZMod (m*n) →+* ZMod n :=
  (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom

/-- Frequency CRT includes the necessary cross-modulus multipliers.
Ordinary residue CRT without these multipliers does not split the standard
additive character with the desired normalization. -/
@[expose] def frequencyMerge (m n : ℕ) (h : m.Coprime n) :
    ZMod m × ZMod n ≃ ZMod (m*n) :=
  ((ZMod.unitOfCoprime n h.symm).mulLeft.prodCongr
    (ZMod.unitOfCoprime m h).mulLeft).trans (ZMod.chineseRemainder h).symm.toEquiv

lemma actual_frequency_merge_components (m n : ℕ) (h : m.Coprime n)
    (a : ZMod m) (b : ZMod n) :
    ZMod.chineseRemainder h (frequencyMerge m n h (a,b)) = ((n : ZMod m)*a,(m : ZMod n)*b) := by
  simp [frequencyMerge,Units.mulLeft,ZMod.coe_unitOfCoprime]

lemma actual_frequency_merge_formula (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (a : ZMod m) (b : ZMod n) :
    frequencyMerge m n h (a,b) =
      (n : ZMod (m*n))*(a.val : ZMod (m*n))+(m : ZMod (m*n))*(b.val : ZMod (m*n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [actual_frequency_merge_components]
  simp only [map_add,map_mul,map_natCast]
  apply Prod.ext <;> simp [ZMod.natCast_self,ZMod.natCast_zmod_val]

lemma actual_frequency_merge_unit (m n : ℕ) (h : m.Coprime n) (ab : ZMod m × ZMod n) :
    IsUnit (frequencyMerge m n h ab) ↔ IsUnit ab.1 ∧ IsUnit ab.2 := by
  rw [←(ZMod.chineseRemainder h).toMulEquiv.isUnit_map]
  rcases ab with ⟨a,b⟩
  rw [actual_frequency_merge_components,Prod.isUnit_iff]
  have hn : IsUnit (n : ZMod m) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime n h.symm).isUnit
  have hm : IsUnit (m : ZMod n) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime m h).isUnit
  simp only [IsUnit.mul_iff,hn,hm,true_and]

@[expose] def unitPairEquiv (m n : ℕ) :
    {ab : ZMod m × ZMod n // IsUnit ab.1 ∧ IsUnit ab.2} ≃
      {a : ZMod m // IsUnit a} × {b : ZMod n // IsUnit b} where
  toFun ab := (⟨ab.val.1,ab.property.1⟩,⟨ab.val.2,ab.property.2⟩)
  invFun ab := ⟨(ab.1.val,ab.2.val),ab.1.property,ab.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cross-scaled CRT restricts to a bijection of the exact unit
frequency domains, including modulus1. -/
@[expose] def unitFrequencyMerge (m n : ℕ) (h : m.Coprime n) :
    {a : ZMod m // IsUnit a} × {b : ZMod n // IsUnit b} ≃
      {a : ZMod (m*n) // IsUnit a} :=
  (unitPairEquiv m n).symm.trans
    ((frequencyMerge m n h).subtypeEquiv (fun ab => (actual_frequency_merge_unit m n h ab).symm))

lemma actual_unit_frequency_merge_value (m n : ℕ) (h : m.Coprime n)
    (ab : {a : ZMod m // IsUnit a} × {b : ZMod n // IsUnit b}) :
    (unitFrequencyMerge m n h ab).val = frequencyMerge m n h (ab.1.val,ab.2.val) := rfl

@[expose] def residueCRT (m n : ℕ) (h : m.Coprime n) :
    Coordinates (ZMod (m*n)) ≃ Coordinates (ZMod m) × Coordinates (ZMod n) :=
  (ActualOriginalProductQuadric318.coordinateRingEquiv (ZMod.chineseRemainder h)).trans
    (splitCoordinates (ZMod m) (ZMod n))

lemma actual_residue_crt_first (m n : ℕ) (h : m.Coprime n) (x : Coordinates (ZMod (m*n))) :
    (residueCRT m n h x).1 = mapCoordinates (first m n h) x := rfl
lemma actual_residue_crt_second (m n : ℕ) (h : m.Coprime n) (x : Coordinates (ZMod (m*n))) :
    (residueCRT m n h x).2 = mapCoordinates (second m n h) x := rfl

end ActualOriginalFrequencyCRT318
