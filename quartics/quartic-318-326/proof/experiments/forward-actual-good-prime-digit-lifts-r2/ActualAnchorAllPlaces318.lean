module
public import PadicAnchorUniversality318
public section
noncomputable section
namespace ActualAnchorAllPlaces318
open PreparedAnchorLabels318 ActualAnchorRatio318
set_option maxHeartbeats 1000000

/-- The exact ternary form represents every real target by an explicit line
through its real isotropic vector(sqrt2,0,1). -/
theorem real_represents (c : ℝ) : ∃ x y z : ℝ, x^2+6*y^2-2*z^2=c := by
  apply PadicAnchorUniversality318.represent_of_isotropic (Real.sqrt 2) 0 1 c (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  nlinarith

/-- All finite primes are covered on the actual prepared scalar ratio.
There is no omitted support-prime or denominator-prime exceptional set. -/
theorem finite_represents (a : ℤ) (A B N d : ℕ) (hd : d≠0)
    (p : ℕ) [Fact p.Prime] :
    let ns := FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)
    ∃ x y z : ℚ_[p], x^2+6*y^2-2*z^2=((3*(ratio ns N)^2-2:ℚ):ℚ_[p]) := by
  dsimp only
  obtain ⟨hr,h2,h3⟩ := actual_anchor_depths a A B N d hd
  by_cases hp2 : p=2
  · subst p
    obtain ⟨x,hx⟩ := AnchorLocalSquareProduction318.at_two _ hr h2
    exact ⟨x,0,0,by simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero,sub_zero,pow_two] using hx.symm⟩
  by_cases hp3 : p=3
  · subst p
    obtain ⟨x,hx⟩ := AnchorLocalSquareProduction318.at_three _ h3
    exact ⟨x,0,0,by simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero,sub_zero,pow_two] using hx.symm⟩
  have hp5 : 5≤p := by
    have hprime : p.Prime := Fact.out
    have hlo := hprime.two_le
    by_contra! hhi
    interval_cases p <;> norm_num at *
  exact PadicAnchorUniversality318.represents p hp5 _

/-- Local representations over the real place and every actual p-adic field. -/
@[expose] def LocallyRepresented (c : ℚ) : Prop :=
  (∃ x y z : ℝ, x^2+6*y^2-2*z^2=(c:ℝ)) ∧
  ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    ∃ x y z : ℚ_[p], x^2+6*y^2-2*z^2=(c:ℚ_[p])

theorem actual_all_places (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)
    LocallyRepresented (3*(ratio ns N)^2-2) := by
  dsimp only
  refine ⟨real_represents _,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact finite_represents a A B N d hd p

/-- The exact remaining quadratic-form local-global theorem, explicitly an
input here. No axiom or local-to-global inference is hidden in its name. -/
@[expose] def LocalGlobalPrinciple : Prop := ∀ c : ℚ, LocallyRepresented c →
  ∃ X Y Z T : ℚ, (¬(X=0 ∧ Y=0 ∧ Z=0 ∧ T=0)) ∧
    X^2+6*Y^2-2*Z^2=c*T^2

/-- Every local input to the remaining global theorem is now produced on
these actual labels; the retained anisotropy theorem handles the affine chart. -/
theorem actual_homogeneous (hglobal : LocalGlobalPrinciple)
    (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    PhysicalAnchorFromHomogeneous318.Homogeneous
      (FixedArithmeticLabels318.labels a A B (multiplier N d) (multiplier_ne N d hd)) N :=
  hglobal _ (actual_all_places a A B N d hd)

end ActualAnchorAllPlaces318
