module
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualTubeAnnulusChart318
open scoped ContDiff

def annulusBump : ContDiffBump (3/4:ℝ) :=
  ⟨1/4,1/2,by norm_num,by norm_num⟩

def shiftBump : ContDiffBump (0:ℝ) :=
  ⟨1,2,by norm_num,by norm_num⟩

def chartBump : ContDiffBump (0:ℝ) :=
  ⟨1/8,1/4,by norm_num,by norm_num⟩

@[expose] def χ (x : ℝ) : ℝ := annulusBump x
@[expose] def ζ (x : ℝ) : ℝ := shiftBump x
@[expose] def off (x : ℝ) : ℝ := 1-chartBump x

lemma χ_one (u : ℝ) (h₁ : 1/2≤u) (h₂ : u≤1) : χ u=1 := by
  apply annulusBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall,Real.dist_eq]
  change |u-3/4|≤1/4
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma χ_zero_low (u : ℝ) (hu : u≤1/4) : χ u=0 := by
  apply annulusBump.zero_of_le_dist
  rw [Real.dist_eq]
  change (1/2:ℝ)≤|u-3/4|
  rw [abs_of_nonpos (by linarith : u-3/4≤0)]
  linarith

lemma χ_zero_high (u : ℝ) (hu : 5/4≤u) : χ u=0 := by
  apply annulusBump.zero_of_le_dist
  rw [Real.dist_eq]
  change (1/2:ℝ)≤|u-3/4|
  rw [abs_of_nonneg (by linarith : 0≤u-3/4)]
  linarith

lemma ζ_one (u : ℝ) (hu : |u|≤1) : ζ u=1 := by
  apply shiftBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]
  exact hu

lemma off_zero (u : ℝ) (hu : |u|≤1/8) : off u=0 := by
  have h : chartBump u=1 := by
    apply chartBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]
    exact hu
  rw [off,h,sub_self]

lemma off_one (u : ℝ) (hu : 1/4≤|u|) : off u=1 := by
  have h : chartBump u=0 := by
    apply chartBump.zero_of_le_dist
    rw [Real.dist_eq,sub_zero]
    exact hu
  rw [off,h,sub_zero]

/-- The actual two positive norm annuli and physical thin coordinate. -/
@[expose] def tube (τ a b c d v : ℝ) : ℝ :=
  χ (a^2+b^2)*χ (c^2+d^2)*ζ (v/τ)

lemma tube_one (τ a b c d v : ℝ) (h₁ : 1/2≤a^2+b^2) (h₂ : a^2+b^2≤1)
    (h₃ : 1/2≤c^2+d^2) (h₄ : c^2+d^2≤1) (hv : |v/τ|≤1) :
    tube τ a b c d v=1 := by
  simp [tube,χ_one _ h₁ h₂,χ_one _ h₃ h₄,ζ_one _ hv]

/-- A telescoping partition, with no normalization denominator. -/
@[expose] def selector (i : Fin 4) (x y z t : ℝ) : ℝ :=
  if i=0 then off x else if i=1 then (1-off x)*off y else
  if i=2 then (1-off x)*(1-off y)*off z else (1-off x)*(1-off y)*(1-off z)*off t

lemma selector_sum (x y z t : ℝ) :
    selector 0 x y z t + selector 1 x y z t + selector 2 x y z t + selector 3 x y z t =
      1-(1-off x)*(1-off y)*(1-off z)*(1-off t) := by
  norm_num [selector]
  <;> ring

lemma large_coordinate (a b c d : ℝ) (h : 1/4≤a^2+b^2) :
    1/4≤|a-c| ∨ 1/4≤|a+c| ∨ 1/4≤|b-d| ∨ 1/4≤|b+d| := by
  by_contra! hn
  obtain ⟨hx,hy,hz,ht⟩ := hn
  have hx' := abs_lt.mp hx
  have hy' := abs_lt.mp hy
  have hz' := abs_lt.mp hz
  have ht' := abs_lt.mp ht
  have ha : 0≤(1/4-a)*(1/4+a) := mul_nonneg (by linarith) (by linarith)
  have hb : 0≤(1/4-b)*(1/4+b) := mul_nonneg (by linarith) (by linarith)
  nlinarith only [h,ha,hb]

theorem tube_partition (τ a b c d v : ℝ) :
    tube τ a b c d v * (selector 0 (a-c) (a+c) (b-d) (b+d) +
      selector 1 (a-c) (a+c) (b-d) (b+d) + selector 2 (a-c) (a+c) (b-d) (b+d) +
      selector 3 (a-c) (a+c) (b-d) (b+d)) = tube τ a b c d v := by
  rw [selector_sum]
  by_cases h : a^2+b^2≤1/4
  · simp [tube,χ_zero_low _ h]
  · rcases large_coordinate a b c d (by linarith) with hx|hy|hz|ht
    · simp [off_one _ hx]
    · simp [off_one _ hy]
    · simp [off_one _ hz]
    · simp [off_one _ ht]

/-- Undo the coordinate swap for each chart. The first and second planes
can be swapped; the distinguished coordinate is exactly X in each case. -/
@[expose] def undo (i : Fin 4) (X Y Z T : ℝ) : ℝ×ℝ×ℝ×ℝ :=
  if i=0 then (X,Y,Z,T) else if i=1 then (Y,X,Z,T) else
  if i=2 then (Z,T,X,Y) else (Z,T,Y,X)

@[expose] def eliminated (κ X Z T V : ℝ) : ℝ := (κ*V^2-Z*T)/X

/-- Explicit value bound for the only rational normalized coordinate.
Its first, second and zero higher derivatives have the same bound on paper. -/
lemma eliminated_abs (κ X Z T V : ℝ) (hX : 1/8≤|X|)
    (hZ : |Z|≤4) (hT : |T|≤4) (hV : |V|≤2) :
    |eliminated κ X Z T V|≤160*(1+|κ|) := by
  have hV2 : |V^2|≤4 := by
    rw [abs_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hV) (by positivity : 0≤2+|V|)]
  have hZT : |Z*T|≤16 := by
    rw [abs_mul]
    exact (mul_le_mul hZ hT (abs_nonneg _) (by norm_num : (0:ℝ)≤4)).trans (by norm_num)
  have hn : |κ*V^2-Z*T|≤4*|κ|+16 := by
    calc
      _ ≤ |κ*V^2|+|Z*T| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (κ*V^2) (-(Z*T))
      _ ≤ |κ| * 4 + 16 := by
        rw [abs_mul κ (V ^ 2)]
        exact add_le_add (mul_le_mul_of_nonneg_left hV2 (abs_nonneg _)) hZT
      _ = _ := by ring
  unfold eliminated
  rw [abs_div]
  apply (div_le_iff₀ ((by norm_num : (0:ℝ)<1/8).trans_le hX)).mpr
  calc
    _ ≤ 4*|κ|+16 := hn
    _ ≤ (160*(1+|κ|))*(1/8) := by nlinarith [abs_nonneg κ]
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

/-- The signed chart section on normalized variables. It is identically
zero near X=0 due to its selector, not due to a cancelling denominator. -/
@[expose] def sectionWeight (κ τ : ℝ) (i : Fin 4) (X Z T V : ℝ) : ℝ :=
  let p := undo i X (eliminated κ X Z T V) Z T
  let x := p.1
  let y := p.2.1
  let z := p.2.2.1
  let t := p.2.2.2
  tube τ ((x+y)/2) ((z+t)/2) ((y-x)/2) ((t-z)/2) V * selector i x y z t

theorem section_zero_small (κ τ : ℝ) (i : Fin 4) (X Z T V : ℝ) (hX : |X|≤1/8) :
    sectionWeight κ τ i X Z T V=0 := by
  fin_cases i <;> norm_num [sectionWeight,undo,selector,off_zero _ hX]

end ActualTubeAnnulusChart318
