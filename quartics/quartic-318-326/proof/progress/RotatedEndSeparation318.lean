module
public import RotatedHomeomorph318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups
namespace RotatedEndSeparation318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Every integral upper triangular determinant-one matrix preserves height,
including its negative-unipotent branch. -/
theorem im_smul_of_lower_left_zero (k:SL(2,ℤ)) (hc:k 1 0=0) (tau:UpperHalfPlane) :
    (k•tau).im=tau.im := by
  have hd:k 0 0*k 1 1=1 := by
    have := k.det_coe
    rwa [Matrix.det_fin_two,hc,mul_zero,sub_zero] at this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha,hd⟩ | ⟨ha,hd⟩
  all_goals rw [ModularGroup.im_smul_eq_div_normSq]
  all_goals simp [ModularGroup.denom_apply,hc,hd,Complex.normSq_apply]

/-- If two genuine rotated high regions meet, a genuine Gamma1 element
identifies their rational ends, and the intervening matrix preserves height. -/
theorem intersection_matrix (N:ℕ) (g h:SL(2,ℤ)) (A B:ℝ) (hA:1≤A) (hB:1≤B)
    (hi:¬Disjoint (FiniteCuspCoverage318.cuspRegion N g A)
      (FiniteCuspCoverage318.cuspRegion N h B)) :
    ∃gamma:CongruenceSubgroup.Gamma1 N,(h⁻¹*gamma.val*g) 1 0=0 := by
  obtain ⟨b,hbg,hbh⟩:=Set.not_disjoint_iff.mp hi
  obtain ⟨tau,htau,hgtau⟩:=hbg
  obtain ⟨sigma,hsigma,hhsigma⟩:=hbh
  have he:quotientMap N (h•sigma)=quotientMap N (g•tau):=hhsigma.trans hgtau.symm
  obtain ⟨delta,hd⟩:=MulAction.orbitRel_apply.mp (Quotient.exact he)
  obtain ⟨gamma,hgamma⟩:=delta.property
  have hact:gamma.val•(g•tau)=h•sigma := by
    change (delta.val:DerivativeCocycle318.G)•(g•tau)=h•sigma at hd
    rw [←hgamma] at hd
    exact hd
  have hk:(h⁻¹*gamma.val*g)•tau=sigma := by
    rw [mul_smul,mul_smul,hact,inv_smul_smul]
  refine ⟨gamma,RotatedStabilizer318.lower_left_zero_of_high _ tau (lt_of_le_of_lt hA htau) ?_⟩
  rw [hk]
  exact lt_of_le_of_lt hB hsigma

theorem region_subset_of_matrix (N:ℕ) (g h:SL(2,ℤ))
    (gamma:CongruenceSubgroup.Gamma1 N) (hc:(h⁻¹*gamma.val*g) 1 0=0) (A:ℝ) :
    FiniteCuspCoverage318.cuspRegion N g A⊆FiniteCuspCoverage318.cuspRegion N h A := by
  rintro b ⟨tau,htau,rfl⟩
  refine ⟨(h⁻¹*gamma.val*g)•tau,?_,?_⟩
  · change A<((h⁻¹*gamma.val*g)•tau).im
    rw [im_smul_of_lower_left_zero _ hc]
    exact htau
  · have he:h•((h⁻¹*gamma.val*g)•tau)=gamma.val•(g•tau) := by
      simp only [mul_smul,smul_inv_smul]
    change quotientMap N (h•((h⁻¹*gamma.val*g)•tau))=quotientMap N (g•tau)
    rw [he]
    exact FiniteCuspCoverage318.quotient_smul N gamma (g•tau)

/-- Intersecting high cusp regions agree at every common height. This excludes
doubled end representatives before any cusp attachment is formed. -/
theorem regions_equal_of_intersect (N:ℕ) (g h:SL(2,ℤ)) (A B:ℝ) (hA:1≤A) (hB:1≤B)
    (hi:¬Disjoint (FiniteCuspCoverage318.cuspRegion N g A)
      (FiniteCuspCoverage318.cuspRegion N h B)) (C:ℝ) :
    FiniteCuspCoverage318.cuspRegion N g C=FiniteCuspCoverage318.cuspRegion N h C := by
  obtain ⟨gamma,hgamma⟩:=intersection_matrix N g h A B hA hB hi
  obtain ⟨delta,hdelta⟩:=intersection_matrix N h g B A hB hA (fun hd=>hi hd.symm)
  exact Set.Subset.antisymm (region_subset_of_matrix N g h gamma hgamma C)
    (region_subset_of_matrix N h g delta hdelta C)

/-- The actual rotated height-two neighborhoods are equal or disjoint. -/
theorem neighborhoods_equal_or_disjoint (N:ℕ) (g h:SL(2,ℤ)) :
    RotatedProjection318.neighborhood N g=RotatedProjection318.neighborhood N h ∨
      Disjoint (RotatedProjection318.neighborhood N g) (RotatedProjection318.neighborhood N h) := by
  by_cases hd:Disjoint (RotatedProjection318.neighborhood N g) (RotatedProjection318.neighborhood N h)
  · exact Or.inr hd
  · exact Or.inl (regions_equal_of_intersect N g h 2 2 (by norm_num) (by norm_num) hd 2)

end RotatedEndSeparation318
