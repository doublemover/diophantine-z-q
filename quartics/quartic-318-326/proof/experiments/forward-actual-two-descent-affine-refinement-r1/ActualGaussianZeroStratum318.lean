module
public import ActualTernaryLevelCount318
public section
noncomputable section
namespace ActualGaussianZeroStratum318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceBoxCount318
open IntegerResidueBoxCount318 TriangularLatticeBoxCount318 LiteralTernaryReduction318
open ActualTernaryLevelCount318 ActualDivisorSubpower318
open OriginalBadSliceLogWeight318 OriginalWeightedSelberg318
set_option maxHeartbeats 14000000

/-- Every actual original source point on R=0, WITHOUT nonzero-label or
prime-obstruction restrictions. Both zero-label axes and their intersection
are included, so this safely bounds the entire discarded R=0 stratum. -/
@[expose] def ZeroSource (B : ℕ) (κ : ℤ) :=
  {v : Quadric κ // InBox B v.1 ∧ R κ (project v.1)=0}

lemma equal_or_opposite (B : ℕ) (κ : ℤ) (v : ZeroSource B κ) :
    v.1.1.2.1.1=v.1.1.1.1 ∨ v.1.1.2.1.1= -v.1.1.1.1 := by
  have hh := factorization κ v.1
  rw [v.2.2] at hh
  dsimp [x0,x1] at hh
  rcases mul_eq_zero.mp hh with h|h
  · right;linarith
  · left;linarith

@[expose] def zeroEncode (B : ℕ) (κ : ℤ) (v : ZeroSource B κ) :
    Bool×Interval B×Level (2*B) κ 0 :=
  (decide (v.1.1.2.1.1=v.1.1.1.1),
    ⟨v.1.1.1.1,Finset.mem_Icc.mpr v.2.1.1⟩,
    ⟨projectedBox B κ (x0 v.1.1) true ⟨⟨v.1,rfl⟩,v.2.1⟩,v.2.2⟩)

lemma zeroEncode_injective (B : ℕ) (κ : ℤ) : Function.Injective (zeroEncode B κ) := by
  intro v u he
  have hs : decide (v.1.1.2.1.1=v.1.1.1.1)=decide (u.1.1.2.1.1=u.1.1.1.1) := congrArg Prod.fst he
  have ha : v.1.1.1.1=u.1.1.1.1 := congrArg (fun z : Bool×Interval B×Level (2*B) κ 0 => z.2.1.1) he
  have hp : project v.1.1=project u.1.1 := congrArg
    (fun z : Bool×Interval B×Level (2*B) κ 0 => coordinates z.2.2.1) he
  have hc : v.1.1.2.1.1=u.1.1.2.1.1 := by
    by_cases hv : v.1.1.2.1.1=v.1.1.1.1
    · have hu : u.1.1.2.1.1=u.1.1.1.1 := by by_contra hh;simp [hv,hh] at hs
      exact hv.trans (ha.trans hu.symm)
    · have hu : u.1.1.2.1.1≠u.1.1.1.1 := by intro hh;simp [hv,hh] at hs
      rw [(equal_or_opposite B κ v).resolve_left hv,(equal_or_opposite B κ u).resolve_left hu,ha]
  have hx := congrArg Prod.fst hp
  have hz := congrArg (fun y : TernaryQuadraticLineCover318.Vector ℤ => y.2.1) hp
  have hw := congrArg (fun y : TernaryQuadraticLineCover318.Vector ℤ => y.2.2) hp
  dsimp [project] at hx hz hw
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext ha (by omega)) (Prod.ext (Prod.ext hc (by omega)) hw)

instance zeroSource_finite (B : ℕ) (κ : ℤ) : Finite (ZeroSource B κ) :=
  Finite.of_injective (zeroEncode B κ) (zeroEncode_injective B κ)

lemma actual_zero_count (B : ℕ) (κ : ℤ) :
    Nat.card (ZeroSource B κ)≤2*(2*B+1)*Nat.card (Level (2*B) κ 0) := by
  have hh := Nat.card_le_card_of_injective (zeroEncode B κ) (zeroEncode_injective B κ)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool,
    Interval,Fintype.card_coe,interval_card,mul_assoc] using hh

/-- Fully constructed count for the actual R=0 source. The bound includes
the zero factorization fibers, not an invalid divisor bound at integer0. -/
@[expose] def zeroBudget (B : ℕ) (κ : ℤ) (δ : ℝ) : ℝ :=
  2*(2*(B:ℝ)+1)*
    ((4*(B:ℝ)+1)*(2*divisorConstant δ*(|(κ:ℝ)|*(2*(B:ℝ))^2)^δ)+4*(4*(B:ℝ)+1))

theorem actual_zero_source_tail (B : ℕ) (κ : ℤ) (hκ : κ≠0) (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (ZeroSource B κ):ℝ)≤zeroBudget B κ δ := by
  have hc : (Nat.card (ZeroSource B κ):ℝ)≤
      2*(2*(B:ℝ)+1)*(Nat.card (Level (2*B) κ 0):ℝ) := by
    exact_mod_cast actual_zero_count B κ
  have hl := mul_le_mul_of_nonneg_left (actual_level_count (2*B) κ 0 hκ δ hδ)
    (by positivity : 0≤2*(2*(B:ℝ)+1))
  exact hc.trans (by simpa [zeroBudget,levelHeight] using hl)

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def mass (B : ℕ) (κ : ℤ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (ZeroSource B κ) := Fintype.ofFinite _
  exact ∑ v : ZeroSource B κ, weight κ γ v.1

theorem actual_weighted_zero_source_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (δ : ℝ) (hδ : 0<δ) (γ : J → ℤ) :
    mass B κ γ≤zeroBudget B κ δ*weightCeiling B γ := by
  classical
  letI : Fintype (ZeroSource B κ) := Fintype.ofFinite _
  have hm : mass B κ γ≤(Nat.card (ZeroSource B κ):ℝ)*weightCeiling B γ := by
    calc
      _ ≤ ∑ _v : ZeroSource B κ, weightCeiling B γ :=
        Finset.sum_le_sum (fun v _ => original_weight_bound B hB κ (x0 v.1.1) true γ
          ⟨⟨v.1,rfl⟩,v.2.1⟩)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  exact hm.trans (mul_le_mul_of_nonneg_right (actual_zero_source_tail B κ hκ δ hδ)
    (weightCeiling_nonneg B hB γ))

end ActualGaussianZeroStratum318
