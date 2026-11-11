module
public import ActualGaussianPatternProjection318
public section
noncomputable section
namespace ActualFiniteGaussianPositionTail318
open scoped BigOperators
open ActualGaussianGrowingCutoff318 ActualGaussianPatternProjection318
set_option maxHeartbeats 15000000
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def Positions (J : Type*) := {q : J×J // q.1≠q.2}
/-- One actual integer cutoff for the ENTIRE fixed coefficient family,
chosen before the two positions, signs, generators or common prime. -/
@[expose] def commonCutoff (c : J → ℤ) (B : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun q : Positions J => cutoff (c q.1.1-c q.1.2) B)
lemma pair_cutoff_le (c : J → ℤ) (B : ℕ) (q : Positions J) :
    cutoff (c q.1.1-c q.1.2) B≤commonCutoff c B :=
  Finset.le_sup (f := fun q : Positions J => cutoff (c q.1.1-c q.1.2) B) (Finset.mem_univ q)

@[expose] def PositionPattern (B Y : ℕ) (c : J → ℤ) :=
  {uw : ℤ×ℤ // ∃ q : Positions J, ∃ z : Pattern B (c q.1.1) (c q.1.2) Y, z.1=uw}
@[expose] def Target (B Y : ℕ) (c : J → ℤ) :=
  Σ q : Positions J, Pattern B (c q.1.1) (c q.1.2) Y
@[expose] def sourceChoice (B Y : ℕ) (c : J → ℤ) (z : PositionPattern B Y c) : Target B Y c :=
  ⟨z.2.choose,z.2.choose_spec.choose⟩
lemma choice_forget (B Y : ℕ) (c : J → ℤ) (z : PositionPattern B Y c) :
    (sourceChoice B Y c z).2.1=z.1 := z.2.choose_spec.choose_spec
lemma choice_injective (B Y : ℕ) (c : J → ℤ) : Function.Injective (sourceChoice B Y c) := by
  intro z z' he
  apply Subtype.ext
  have hh := congrArg (fun v : Target B Y c => v.2.1) he
  simpa only [choice_forget] using hh
instance position_finite (B Y : ℕ) (c : J → ℤ) : Finite (PositionPattern B Y c) :=
  Finite.of_injective (sourceChoice B Y c) (choice_injective B Y c)

@[expose] def positionMass (B Y : ℕ) (c : J → ℤ) : ℝ := by
  classical
  letI : Fintype (PositionPattern B Y c) := Fintype.ofFinite _
  exact ∑ z : PositionPattern B Y c,patternWeight c z.1
@[expose] def positionConstant (c : J → ℤ) : ℝ := by
  classical
  exact ∑ q : Positions J, 4*growingConstant (c q.1.1-c q.1.2) (coefficients c (c q.1.1))

/-- Source patterns are counted ONCE, though positions, signs and
Gaussian generators need not be unique. The target finite sum is an
upper bound and retains the same original product of logarithms. -/
lemma actual_position_partition (B Y : ℕ) (c : J → ℤ) :
    positionMass B Y c≤∑ q : Positions J,patternMass B (c q.1.1) (c q.1.2) Y c := by
  classical
  letI : Fintype (PositionPattern B Y c) := Fintype.ofFinite _
  letI : ∀ q : Positions J, Fintype (Pattern B (c q.1.1) (c q.1.2) Y) := fun _ => Fintype.ofFinite _
  let wt : Target B Y c → ℝ := fun z => patternWeight c z.2.1
  have hh := hasSum_le_inj (sourceChoice B Y c) (choice_injective B Y c)
    (fun z _ => patternWeight_nonneg c z.2.1)
    (fun z => le_of_eq (by dsimp [wt];rw [choice_forget]))
    (hasSum_fintype (fun z : PositionPattern B Y c => patternWeight c z.1)) (hasSum_fintype wt)
  simpa only [Target,wt,Fintype.sum_sigma,positionMass,patternMass] using hh

theorem actual_all_distinct_positions_tail (B : ℕ) (hB : 1≤B) (Y : ℕ)
    (c : J → ℤ) (hc : Function.Injective c) (hY : commonCutoff c B≤Y) :
    positionMass B Y c≤positionConstant c*(B:ℝ)^(3-(1:ℝ)/200) := by
  classical
  have hh := actual_position_partition B Y c
  have hs : (∑ q : Positions J,patternMass B (c q.1.1) (c q.1.2) Y c)≤
      ∑ q : Positions J,
        (4*growingConstant (c q.1.1-c q.1.2) (coefficients c (c q.1.1)))*
          (B:ℝ)^(3-(1:ℝ)/200) := by
    apply Finset.sum_le_sum
    intro q _
    have hneq : c q.1.1≠c q.1.2 := fun he => q.2 (hc he)
    exact actual_pattern_tail B hB _ _ hneq Y ((pair_cutoff_le c B q).trans hY) c
  exact hh.trans (by simpa only [←Finset.sum_mul,positionConstant] using hs)

/-- The interface from literal original generator data to the full
finite-position source. No polynomial or coefficient relabeling is hidden. -/
theorem original_pattern_member (B Y : ℕ) (c : J → ℤ) (i j : J) (hij : i≠j)
    (u w a b d e : ℤ)
    (hfirst : a^2+b^2=u+c i*w^2) (hsecond : d^2+e^2=u+c j*w^2)
    (hbox : LiteralSliceBoxCount318.InBox B ((a,b),(d,e),w))
    (hbad : ∃ s t : Bool, ∃ p : ℕ, p.Prime ∧ Y<p ∧
      (p:ℤ)∣(a+ActualGaussianSignAction318.sign s)^2+b^2 ∧
      (p:ℤ)∣(d+ActualGaussianSignAction318.sign t)^2+e^2) :
    ∃ z : PositionPattern B Y c,z.1=(u,w) := by
  obtain ⟨z,hz⟩ := of_actual_generators B (c i) (c j) u w a b d e Y hfirst hsecond hbox hbad
  exact ⟨⟨(u,w),⟨(i,j),hij⟩,z,hz⟩,rfl⟩

/-- At actual prime values the clipped nonnegative source weight is
literally the manuscript's product of logarithms of those prime norms. -/
theorem actual_prime_weight (c : J → ℤ) (z : ℤ×ℤ)
    (hp : ∀ j,(z.1+c j*z.2^2).natAbs.Prime) :
    patternWeight c z=∏ j,Real.log (((z.1+c j*z.2^2).natAbs:ℝ)) := by
  apply Finset.prod_congr rfl
  intro j _
  have hh : (1:ℝ)≤(z.1+c j*z.2^2).natAbs := by
    exact_mod_cast (show 1≤(z.1+c j*z.2^2).natAbs by have hh := (hp j).two_le;omega)
  rw [max_eq_right hh]

end ActualFiniteGaussianPositionTail318
