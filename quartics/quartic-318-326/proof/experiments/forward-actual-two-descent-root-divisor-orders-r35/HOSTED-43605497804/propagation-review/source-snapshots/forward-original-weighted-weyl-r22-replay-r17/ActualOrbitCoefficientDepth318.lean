module
public import ActualOrbitBranchDepth318
public section
noncomputable section
namespace ActualOrbitCoefficientDepth318
open ConcreteG8Domain (K pair)
open CoherentMultipleCharts318 ActualOrbitBranchDepth318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma half_bound (B s t : ℤ) (a : WithTop ℤ) (hst : t≤s)
    (h : ((2*B+s:ℤ):WithTop ℤ)≤(t:WithTop ℤ)+2•a) : (B:WithTop ℤ)≤a := by
  by_cases ha : a=⊤
  · simp [ha]
  obtain ⟨a',ha'⟩ := WithTop.ne_top_iff_exists.mp ha
  rw [←ha'] at h ⊢
  simp only [two_nsmul] at h
  have hi : 2*B+s≤t+(a'+a') := by exact_mod_cast h
  exact_mod_cast (show B≤a' by omega)

lemma two_coefficients (x : K) (B : ℤ)
    (hv : ((2*B+1:ℤ):WithTop ℤ)≤RamifiedTwo318.place x) :
    (B:WithTop ℤ)≤RamifiedTwo318.rational x.re ∧
      (B:WithTop ℤ)≤RamifiedTwo318.rational x.im := by
  rw [RamifiedTwo318.place_value] at hv
  change ((2*B+1:ℤ):WithTop ℤ)≤RamifiedTwo318.value (pair x.re x.im) at hv
  rw [RamifiedTwo318.pair_value] at hv
  constructor
  · apply half_bound B 1 0 _ (by norm_num)
    simpa only [zero_add] using le_trans hv (min_le_left _ _)
  · exact half_bound B 1 1 _ (by norm_num) (le_trans hv (min_le_right _ _))

lemma three_coefficients (x : K) (B : ℤ)
    (hv : ((2*B:ℤ):WithTop ℤ)≤InertThree318.place x) :
    (B:WithTop ℤ)≤InertThree318.rational x.re ∧
      (B:WithTop ℤ)≤InertThree318.rational x.im := by
  rw [InertThree318.place_value] at hv
  change ((2*B:ℤ):WithTop ℤ)≤InertThree318.value (pair x.re x.im) at hv
  rw [InertThree318.pair_value] at hv
  constructor
  · apply half_bound B 0 0 _ (by norm_num)
    simpa only [add_zero,zero_add] using le_trans hv (min_le_left _ _)
  · apply half_bound B 0 0 _ (by norm_num)
    simpa only [add_zero,zero_add] using le_trans hv (min_le_right _ _)

lemma ramified_rational (x : ℚ) : RamifiedTwo318.rational x=ConcretePadic318.rationalPlace 2 x := by
  by_cases hx : x=0
  · simp [hx]
  · rw [RamifiedTwo318.rational_value x hx,ConcretePadic318.rational_value 2 x hx]

lemma inert_rational (x : ℚ) : InertThree318.rational x=ConcretePadic318.rationalPlace 3 x := by
  by_cases hx : x=0
  · simp [hx]
  · rw [InertThree318.rational_value x hx,ConcretePadic318.rational_value 3 x hx]

/-- Both actual rational chart coefficients tend to the identity in the
ramified topology. The zero index is included with infinite valuations. -/
theorem two_chart (m : ℤ) :
    ∀ x∈[chartU (4*m),chartV (4*m)-1],
      ((1+(padicValInt 2 m:ℤ):ℤ):WithTop ℤ)≤ConcretePadic318.rationalPlace 2 x.re ∧
      ((1+(padicValInt 2 m:ℤ):ℤ):WithTop ℤ)≤ConcretePadic318.rationalPlace 2 x.im := by
  by_cases hm : m=0
  · subst m
    simp
  intro x hx
  simp only [List.mem_cons,List.mem_singleton] at hx
  rcases hx with rfl|rfl
  · have he := two_coefficients (chartU (4*m)) (1+(padicValInt 2 m:ℤ)) (by
      rw [two_u_place m hm]
      exact_mod_cast (show 2*(1+(padicValInt 2 m:ℤ))+1≤7+2*(padicValInt 2 m:ℤ) by omega))
    simpa only [ramified_rational] using he
  · have he := two_coefficients (chartV (4*m)-1) (1+(padicValInt 2 m:ℤ)) (by
      rw [two_v_place m hm]
      exact_mod_cast (show 2*(1+(padicValInt 2 m:ℤ))+1≤26+8*(padicValInt 2 m:ℤ) by omega))
    simpa only [ramified_rational] using he

/-- The same actual plus identity chart at the inert prime. No splitting
hypothesis or independent choice of the v sign is used. -/
theorem three_chart (m : ℤ) :
    ∀ x∈[chartU (4*m),chartV (4*m)-1],
      ((1+(padicValInt 3 m:ℤ):ℤ):WithTop ℤ)≤ConcretePadic318.rationalPlace 3 x.re ∧
      ((1+(padicValInt 3 m:ℤ):ℤ):WithTop ℤ)≤ConcretePadic318.rationalPlace 3 x.im := by
  by_cases hm : m=0
  · subst m
    simp
  intro x hx
  simp only [List.mem_cons,List.mem_singleton] at hx
  rcases hx with rfl|rfl
  · have he := three_coefficients (chartU (4*m)) (1+(padicValInt 3 m:ℤ)) (by
      rw [three_u_place m hm]
      exact_mod_cast (show 2*(1+(padicValInt 3 m:ℤ))≤2+2*(padicValInt 3 m:ℤ) by omega))
    simpa only [inert_rational] using he
  · have he := three_coefficients (chartV (4*m)-1) (1+(padicValInt 3 m:ℤ)) (by
      rw [three_v_place m hm]
      exact_mod_cast (show 2*(1+(padicValInt 3 m:ℤ))≤8+8*(padicValInt 3 m:ℤ) by omega))
    simpa only [inert_rational] using he

end ActualOrbitCoefficientDepth318
