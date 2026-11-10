module
public import ActualGaussianZeroStratum318
public section
noncomputable section
namespace ActualOriginalLevelSource318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceBoxCount318
open IntegerResidueBoxCount318 TriangularLatticeBoxCount318 LiteralTernaryReduction318
open ActualIntegerFactorPairs318 ActualTernaryLevelCount318 ActualDivisorSubpower318
set_option maxHeartbeats 14000000

/-- Actual original five-coordinate source on a FIXED integer value ofR. -/
@[expose] def ValueSource (B : ℕ) (κ v : ℤ) :=
  {y : Quadric κ // InBox B y.1 ∧ R κ (project y.1)=v}

@[expose] def valueEncode (B : ℕ) (κ v : ℤ) (y : ValueSource B κ v) :
    Pairs (2*B) v×Level (2*B) κ v := by
  obtain ⟨ha,hb,hc,hd,hw⟩ := y.2.1
  refine (⟨(⟨x0 y.1.1,?_⟩,⟨x1 y.1.1,?_⟩),?_⟩,
    ⟨projectedBox B κ (x0 y.1.1) true ⟨⟨y.1,rfl⟩,y.2.1⟩,y.2.2⟩)
  · apply Finset.mem_Icc.mpr
    dsimp [x0]
    push_cast
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    dsimp [x1]
    push_cast
    constructor <;> omega
  · exact (factorization κ y.1).trans y.2.2

lemma valueEncode_injective (B : ℕ) (κ v : ℤ) : Function.Injective (valueEncode B κ v) := by
  intro y z he
  have ha := congrArg (fun u : Pairs (2*B) v×Level (2*B) κ v => u.1.1.1.1) he
  have hc := congrArg (fun u : Pairs (2*B) v×Level (2*B) κ v => u.1.1.2.1) he
  have hx := congrArg (fun u : Pairs (2*B) v×Level (2*B) κ v => (coordinates u.2.1).1) he
  have hz := congrArg (fun u : Pairs (2*B) v×Level (2*B) κ v => (coordinates u.2.1).2.1) he
  have hw := congrArg (fun u : Pairs (2*B) v×Level (2*B) κ v => (coordinates u.2.1).2.2) he
  change x0 y.1.1=x0 z.1.1 at ha
  change x1 y.1.1=x1 z.1.1 at hc
  change (project y.1.1).1=(project z.1.1).1 at hx
  change (project y.1.1).2.1=(project z.1.1).2.1 at hz
  change (project y.1.1).2.2=(project z.1.1).2.2 at hw
  dsimp [x0,x1,project] at ha hc hx hz hw
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext (by omega) (by omega)) (Prod.ext (Prod.ext (by omega) (by omega)) hw)

instance valueSource_finite (B : ℕ) (κ v : ℤ) : Finite (ValueSource B κ v) :=
  Finite.of_injective (valueEncode B κ v) (valueEncode_injective B κ v)

lemma actual_value_abs (B : ℕ) (κ v : ℤ) (y : ValueSource B κ v) :
    |v|≤4*(B:ℤ)^2 := by
  let e := valueEncode B κ v y
  have h0 := Finset.mem_Icc.mp e.1.1.1.2
  have h1 := Finset.mem_Icc.mp e.1.1.2.2
  have ha : |e.1.1.1.1|≤(2*B:ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using abs_le.mpr h0
  have hb : |e.1.1.2.1|≤(2*B:ℤ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using abs_le.mpr h1
  have hh := mul_le_mul ha hb (abs_nonneg _) (by positivity : (0:ℤ)≤2*B)
  rw [←abs_mul,e.1.2] at hh
  nlinarith only [hh]

@[expose] def valueBudget (B : ℕ) (κ : ℤ) (δ : ℝ) : ℝ :=
  (2*divisorConstant δ*(4*(B:ℝ)^2)^δ)*
    ((4*(B:ℝ)+1)*(2*divisorConstant δ*(4*(|(κ:ℝ)|+1)*(B:ℝ)^2)^δ)+4*(4*(B:ℝ)+1))

lemma valueBudget_nonneg (B : ℕ) (κ : ℤ) (δ : ℝ) (hδ : 0<δ) :
    0≤valueBudget B κ δ := by
  have hd := divisorConstant_pos δ hδ
  dsimp [valueBudget]
  positivity

/-- Uniform actual original fixed-NONZERO-value source count. The label
factorizations and true original ternary level fibers are both retained. -/
theorem actual_value_source_count (B : ℕ) (κ v : ℤ) (hκ : κ≠0) (hv : v≠0)
    (hvB : |v|≤4*(B:ℤ)^2) (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (ValueSource B κ v):ℝ)≤valueBudget B κ δ := by
  have hc : (Nat.card (ValueSource B κ v):ℝ)≤
      (Nat.card (Pairs (2*B) v):ℝ)*(Nat.card (Level (2*B) κ v):ℝ) := by
    have hh := Nat.card_le_card_of_injective (valueEncode B κ v) (valueEncode_injective B κ v)
    simpa only [Nat.card_prod,Nat.cast_mul] using (show (Nat.card (ValueSource B κ v):ℝ)≤
      (Nat.card (Pairs (2*B) v×Level (2*B) κ v):ℝ) by exact_mod_cast hh)
  have hp : (Nat.card (Pairs (2*B) v):ℝ)≤2*(v.natAbs.divisors.card:ℝ) := by
    exact_mod_cast actual_factor_count (2*B) v hv
  have hd := actual_divisor_subpower δ hδ v.natAbs (Int.natAbs_ne_zero.mpr hv)
  have habs : (v.natAbs:ℝ)=|(v:ℝ)| := by exact_mod_cast Int.natCast_natAbs v
  have hvR : |(v:ℝ)|≤4*(B:ℝ)^2 := by exact_mod_cast hvB
  have hpow := Real.rpow_le_rpow (abs_nonneg (v:ℝ)) hvR hδ.le
  rw [habs] at hd
  have hm := mul_le_mul_of_nonneg_left hpow (divisorConstant_pos δ hδ).le
  have hpair : (Nat.card (Pairs (2*B) v):ℝ)≤2*divisorConstant δ*(4*(B:ℝ)^2)^δ := by
    nlinarith only [hp,hd,hm]
  have hH : levelHeight (2*B) κ v≤4*(|(κ:ℝ)|+1)*(B:ℝ)^2 := by
    dsimp [levelHeight]
    push_cast
    nlinarith only [hvR]
  have hH0 : 0≤levelHeight (2*B) κ v := by dsimp [levelHeight];positivity
  have hHpow := Real.rpow_le_rpow hH0 hH hδ.le
  have hHm := mul_le_mul_of_nonneg_left hHpow
    (by have h := divisorConstant_pos δ hδ;positivity : 0≤(4*(B:ℝ)+1)*(2*divisorConstant δ))
  have hl := actual_level_count (2*B) κ v hκ δ hδ
  push_cast at hl
  have hlevel : (Nat.card (Level (2*B) κ v):ℝ)≤
      (4*(B:ℝ)+1)*(2*divisorConstant δ*(4*(|(κ:ℝ)|+1)*(B:ℝ)^2)^δ)+4*(4*(B:ℝ)+1) := by
    nlinarith only [hl,hHm]
  exact hc.trans (mul_le_mul hpair hlevel (by positivity) (by
    have h := divisorConstant_pos δ hδ
    positivity))

end ActualOriginalLevelSource318
