module
public import OriginalGlobalBadMass318
public section
noncomputable section
namespace OriginalGlobalBadSource318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceBoxCount318 LiteralSliceModulus318
open OriginalBadSlicePointTail318 OriginalBadSliceLogWeight318 OriginalGlobalBadMass318
open OriginalThreeDimensionalTransference318 LiteralTernaryReduction318
set_option maxHeartbeats 2500000

@[expose] def labelOf (side : Bool) (v : Coordinates ℤ) : ℤ := if side then x0 v else x1 v

lemma actual_label_mem (B : ℕ) (side : Bool) (v : Coordinates ℤ) (hv : InBox B v)
    (hn : labelOf side v≠0) : labelOf side v∈labels B := by
  apply Finset.mem_erase.mpr
  refine ⟨hn,Finset.mem_Icc.mpr ?_⟩
  obtain ⟨ha,hb,hc,hd,hw⟩ := hv
  cases side <;> dsimp [labelOf,x0,x1] at * <;> constructor <;> omega

/-- ACTUAL original five-coordinate points in the source quadric and box,
with nonzero chosen chart coordinate and an exceptional containing lattice.
The lattice parameter is existential, so a point is counted once even if
it belongs to several exceptional lattices. -/
@[expose] def GlobalBad (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :=
  {v : Quadric κ // InBox B v.1 ∧ labelOf side v.1≠0 ∧
    ∃ s : ∀ i : PrimeIndex κ (labelOf side v.1), Option (ZMod (prime κ (labelOf side v.1) i)),
      LargeThird (prime κ (labelOf side v.1)) κ s T ∧
        project v.1∈literalLattice (prime κ (labelOf side v.1)) κ s}

@[expose] def SlicedBad (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :=
  (t : ↥(labels B)) × BadSlice B κ t.1 side T

@[expose] def toSlices (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :
    GlobalBad B κ side T → SlicedBad B κ side T := fun v =>
  ⟨⟨labelOf side v.1.1,actual_label_mem B side v.1.1 v.2.1 v.2.2.1⟩,
    ⟨⟨⟨v.1,rfl⟩,v.2.1⟩,v.2.2.2⟩⟩

@[expose] def fromSlices (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :
    SlicedBad B κ side T → GlobalBad B κ side T := by
  rintro ⟨⟨t,ht⟩,⟨⟨⟨v,hv⟩,hb⟩,hex⟩⟩
  change labelOf side v.1=t at hv
  subst t
  exact ⟨v,hb,label_ne_zero B _ ht,hex⟩

/-- Unique original chart labels make this a true equivalence, not an
incidence overcount. This is separate from the earlier overlap-safe lattice
parameter estimate inside each fixed slice. -/
@[expose] def sourceEquiv (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :
    GlobalBad B κ side T ≃ SlicedBad B κ side T where
  toFun := toSlices B κ side T
  invFun := fromSlices B κ side T
  left_inv := by
    intro v
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨t,ht⟩,⟨⟨⟨v,hv⟩,hb⟩,hex⟩⟩
    change labelOf side v.1=t at hv
    subst t
    rfl

instance globalBad_finite (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) :
    Finite (GlobalBad B κ side T) :=
  Finite.of_injective (sourceEquiv B κ side T) (sourceEquiv B κ side T).injective

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def sourceMass (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (GlobalBad B κ side T) := Fintype.ofFinite _
  exact ∑ v : GlobalBad B κ side T, OriginalWeightedSelberg318.weight κ γ v.1

/-- Exact mass identity for all actual original source points: neither
source-point multiplicities nor label signs are discarded. -/
theorem source_mass_eq (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) (γ : J → ℤ) :
    sourceMass B κ side T γ=totalMass B κ side T γ := by
  classical
  letI : ∀ t : ↥(labels B), Fintype (BadSlice B κ t.1 side T) := fun _ => Fintype.ofFinite _
  letI : Fintype (GlobalBad B κ side T) := Fintype.ofFinite _
  change (∑ v : GlobalBad B κ side T, OriginalWeightedSelberg318.weight κ γ v.1)=_
  calc
    _ = ∑ v : SlicedBad B κ side T, OriginalWeightedSelberg318.weight κ γ v.2.1.1.1 :=
      Equiv.sum_comp (sourceEquiv B κ side T) _
    _ = ∑ t : ↥(labels B), ∑ v : BadSlice B κ t.1 side T,
        OriginalWeightedSelberg318.weight κ γ v.1.1.1 := by rw [Fintype.sum_sigma]
    _ = totalMass B κ side T γ := by
      simp only [totalMass,logarithmicMass,Finset.sum_coe_sort]

/-- The constructed threshold B^(3/4), on the actual original source,
gives the bad contribution O(B^(11/4+δ)) times the explicit original
logarithmic weight ceiling. No free bad-set bound occurs in the inputs. -/
theorem actual_three_quarter_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (side : Bool)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    sourceMass B κ side ((B:ℝ)^((3:ℝ)/4)) γ≤
      tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*weightCeiling B γ := by
  have hb : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have hT : 0<(B:ℝ)^((3:ℝ)/4) := Real.rpow_pos_of_pos hb _
  have h := power_weighted_tail B hB κ side ((B:ℝ)^((3:ℝ)/4)) hT γ δ hδ
  rw [←source_mass_eq] at h
  apply (mul_le_mul_right (pow_pos hT 3)).mp
  calc
    _ ≤ tailConstant δ*(B:ℝ)^((5:ℝ)+δ)*weightCeiling B γ := h
    _ = (tailConstant δ*(B:ℝ)^((11:ℝ)/4+δ)*weightCeiling B γ)*
        ((B:ℝ)^((3:ℝ)/4))^3 := by
      rw [←Real.rpow_mul_natCast hb.le]
      have he : (5:ℝ)+δ=((11:ℝ)/4+δ)+((3:ℝ)/4)*3 := by ring
      rw [he,Real.rpow_add hb]
      ring

end OriginalGlobalBadSource318
