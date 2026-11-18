module
public import ActualAnchorAllPlaces318
public import ActualAnchorCoefficientCongruences318
public import LegendreSquarefreeCRT318
public section
noncomputable section
namespace ActualNormalizedAnchorLocalData318

/-- Clearing the actual reduced rational denominator gives the normalized
split local vector, whose T-coordinate is the nonzero square factor e.
No local point, integrality or primitive-vector premise is added beyond
the supplied affine representation of the original actual radicand. -/
theorem split_local_of_affine (r : ℚ) (e C : ℤ) (he0 : e≠0)
    (he : e^2*C=3*r.num^2-2*(r.den:ℤ)^2)
    (p : ℕ) [Fact p.Prime] (x y z : ℚ_[p])
    (hpoint : x^2+6*y^2-2*z^2=((3*r^2-2:ℚ):ℚ_[p])) :
    ∃ X Z T Y : ℚ_[p], ¬(X=0 ∧ Z=0 ∧ T=0 ∧ Y=0) ∧
      X^2-2*Z^2=(C:ℚ_[p])*T^2-6*Y^2 := by
  have hd : (r.den:ℚ)≠0 := by exact_mod_cast r.den_ne_zero
  have hclear : (r.den:ℚ)^2*(3*r^2-2)=((e^2*C:ℤ):ℚ) := by
    rw [he]
    calc
      (r.den:ℚ)^2*(3*r^2-2)=
          (r.den:ℚ)^2*(3*((r.num:ℚ)/(r.den:ℚ))^2-2) := by rw [Rat.num_div_den]
      _=((3*r.num^2-2*(r.den:ℤ)^2:ℤ):ℚ) := by
        push_cast
        field_simp [hd] <;> ring
  have hclear_p := congrArg (fun a : ℚ => (a:ℚ_[p])) hclear
  push_cast at hclear_p
  have heP : (e:ℚ_[p])≠0 := by exact_mod_cast he0
  refine ⟨(r.den:ℚ_[p])*x,(r.den:ℚ_[p])*z,(e:ℚ_[p]),(r.den:ℚ_[p])*y,?_,?_⟩
  · rintro ⟨_,_,hT,_⟩
    exact heP hT
  · push_cast at hpoint
    linear_combination (r.den:ℚ_[p])^2*hpoint+hclear_p

/-- Actual prepared labels produce one signed squarefree normalized
coefficient, its splitting-six prime conditions, and nonzero split local
vectors at every prime. This is target-specific preparation, not a universal
local-global hypothesis and not a rational anchor. -/
theorem prepared_normalized_local_data (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B
      (PreparedAnchorLabels318.multiplier N d) (PreparedAnchorLabels318.multiplier_ne N d hd)
    let r := ActualAnchorRatio318.ratio ns N
    ∃ e C : ℤ, e≠0 ∧ C≠0 ∧ Squarefree C ∧ C%24=1 ∧
      e^2*C=3*r.num^2-2*(r.den:ℤ)^2 ∧
      (∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p)) ∧
      (∀ p [Fact p.Prime], ∃ X Z T Y : ℚ_[p],
        ¬(X=0 ∧ Z=0 ∧ T=0 ∧ Y=0) ∧ X^2-2*Z^2=(C:ℚ_[p])*T^2-6*Y^2) := by
  dsimp only
  let ns := FixedArithmeticLabels318.labels a A B
    (PreparedAnchorLabels318.multiplier N d) (PreparedAnchorLabels318.multiplier_ne N d hd)
  let r := ActualAnchorRatio318.ratio ns N
  have hmod : (3*r.num^2-2*(r.den:ℤ)^2)%24=1 :=
    ActualAnchorCoefficientCongruences318.prepared_coefficient_one_mod_twentyfour a A B N d hd
  have hcoeff : 3*r.num^2-2*(r.den:ℤ)^2≠0 := by
    intro hz
    rw [hz] at hmod
    norm_num at hmod
  obtain ⟨e,C,he0,hC0,he,hCsf,_⟩ := LegendreSquarefreeCRT318.normalize _ hcoeff
  have hC24 : C%24=1 := ActualAnchorCoefficientCongruences318.square_factor_one_mod_twentyfour
    e C (by rw [he]; exact hmod)
  refine ⟨e,C,he0,hC0,hCsf,hC24,he,?_,?_⟩
  · intro p hp hdiv
    exact ActualAnchorCoefficientCongruences318.normalized_prime_splits_six r e C he hC24 p hdiv
  · intro p hp
    obtain ⟨x,y,z,hpoint⟩ := ActualAnchorAllPlaces318.finite_represents a A B N d hd p
    exact split_local_of_affine r e C he0 he p x y z hpoint

end ActualNormalizedAnchorLocalData318
