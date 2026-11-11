module
public import ActualThreeCuspWidths318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups
namespace ActualThreeCuspExhaustion318
open RotatedProjection318 RotatedEndSeparation318
set_option maxHeartbeats 0

/-- Over F3 every nonzero residue is a sign. -/
lemma residue_sign (x : ZMod 3) (hx : x ≠ 0) : x=1 ∨ x = -1 := by
  fin_cases x
  · exact (hx rfl).elim
  · exact Or.inl rfl
  · right
    change (2:ZMod 3) = -1
    decide

/-- At level three a matrix whose lower-left entry is zero modulo three
belongs to Gamma1(3) up to its central sign. -/
lemma gamma1_or_neg (g : SL(2,ℤ)) (hc : (g 1 0 : ZMod 3)=0) :
    g ∈ CongruenceSubgroup.Gamma1 3 ∨ -g ∈ CongruenceSubgroup.Gamma1 3 := by
  have hd : (g 0 0 : ZMod 3)*(g 1 1 : ZMod 3)=1 := by
    have hh : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      have hh := g.det_coe
      rw [Matrix.det_fin_two] at hh
      exact hh
    have hh' := congrArg (Int.castRingHom (ZMod 3)) hh
    simpa [hc] using hh'
  have ha0 : (g 0 0 : ZMod 3) ≠ 0 := by intro h; simp [h] at hd
  rcases residue_sign _ ha0 with ha | ha
  · left
    exact (CongruenceSubgroup.Gamma1_mem 3 g).mpr ⟨ha,by simpa [ha] using hd,hc⟩
  · right
    have hb : (g 1 1 : ZMod 3) = -1 := by
      rw [ha] at hd
      linear_combination -hd
    apply (CongruenceSubgroup.Gamma1_mem 3 (-g)).mpr
    simpa [Matrix.SpecialLinearGroup.coe_neg,ha,hb,hc]

/-- Upper triangular changes of the high coordinate and actual Gamma1
left translation preserve precisely the same original cusp neighborhood. -/
lemma neighborhood_eq_of_upper (g h k : SL(2,ℤ)) (hc : k 1 0=0)
    (hk : h*k*g⁻¹ ∈ CongruenceSubgroup.Gamma1 3 ∨
      -(h*k*g⁻¹) ∈ CongruenceSubgroup.Gamma1 3) :
    neighborhood 3 g=neighborhood 3 h := by
  apply regions_equal_of_intersect 3 g h 2 2 (by norm_num) (by norm_num) _ 2
  obtain ⟨b,tau,htau,rfl⟩ := FiniteCuspEnds318.region_nonempty 3 g 2
  apply Set.not_disjoint_iff.mpr
  refine ⟨quotientMap 3 (g•tau),⟨tau,htau,rfl⟩,⟨k•tau,?_,?_⟩⟩
  · change 2 < (k•tau).im
    rw [im_smul_of_lower_left_zero k hc]
    exact htau
  · have he : (h*k*g⁻¹)•(g•tau)=h•(k•tau) := by
      simp only [mul_smul,inv_smul_smul]
    rcases hk with hk | hk
    · exact (congrArg (quotientMap 3) he).symm.trans
        (FiniteCuspCoverage318.quotient_smul 3 ⟨_,hk⟩ (g•tau))
    · have hen : (-(h*k*g⁻¹))•(g•tau)=h•(k•tau) := by
        rw [ModularGroup.SL_neg_smul]
        exact he
      exact (congrArg (quotientMap 3) hen).symm.trans
        (FiniteCuspCoverage318.quotient_smul 3 ⟨_,hk⟩ (g•tau))

lemma S_translation_lower_left (g : SL(2,ℤ)) (n : ℤ) :
    ((ModularGroup.S*ModularGroup.T^n*g⁻¹) 1 0 : ZMod 3)=
      (g 1 1 : ZMod 3)-(n : ZMod 3)*(g 1 0 : ZMod 3) := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,ModularGroup.coe_S,ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  ring

/-- Literal matrix congruences classify every actual rotated cusp region,
without counting generic j fibers or assuming a compactification. -/
theorem neighborhood_classification (g : SL(2,ℤ)) :
    neighborhood 3 g=neighborhood 3 1 ∨
      neighborhood 3 g=neighborhood 3 ModularGroup.S := by
  by_cases hc : (g 1 0 : ZMod 3)=0
  · left
    apply neighborhood_eq_of_upper g 1 1 (by simp)
    have hi : (g⁻¹ 1 0 : ZMod 3)=0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using neg_eq_zero.mpr hc
    simpa using gamma1_or_neg g⁻¹ hi
  · right
    rcases residue_sign _ hc with hc | hc
    · apply neighborhood_eq_of_upper g ModularGroup.S (ModularGroup.T^(g 1 1))
        (by simp [ModularGroup.coe_T_zpow])
      apply gamma1_or_neg
      rw [S_translation_lower_left,hc]
      ring
    · apply neighborhood_eq_of_upper g ModularGroup.S (ModularGroup.T^(-g 1 1))
        (by simp [ModularGroup.coe_T_zpow])
      apply gamma1_or_neg
      rw [S_translation_lower_left,hc]
      push_cast
      ring

/-- Complete set equality for the original rotated high cusp neighborhoods. -/
theorem neighborhood_range : Set.range (neighborhood 3) =
    {neighborhood 3 1,neighborhood 3 ModularGroup.S} := by
  ext U
  constructor
  · rintro ⟨g,rfl⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using neighborhood_classification g
  · rintro (rfl|rfl)
    · exact ⟨1,rfl⟩
    · exact ⟨ModularGroup.S,rfl⟩

lemma neighborhood_left_gamma (gamma : CongruenceSubgroup.Gamma1 3) (g : SL(2,ℤ)) :
    neighborhood 3 (gamma.val*g)=neighborhood 3 g := by
  unfold neighborhood rotatedMap
  congr 1
  funext tau
  rw [mul_smul,FiniteCuspCoverage318.quotient_smul]

/-- The finite selected representative set contains the same actual end
neighborhood for every rotation, not merely a subset of possible ends. -/
lemma neighborhood_mem_ends (g : SL(2,ℤ)) :
    neighborhood 3 g ∈ FiniteCuspEnds318.endRegions 3 := by
  obtain ⟨r,hr,gamma,he⟩ := FiniteCuspCoverage318.rotations_cover 3 g
  rw [he,neighborhood_left_gamma]
  exact ⟨r,hr,rfl⟩

lemma endRegions_eq_range : FiniteCuspEnds318.endRegions 3=Set.range (neighborhood 3) := by
  ext U
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨r,rfl⟩
  · rintro ⟨g,rfl⟩
    exact neighborhood_mem_ends g

/-- Exhaustive classification of the exact original finite cusp-end object. -/
theorem endRegions_eq_pair : FiniteCuspEnds318.endRegions 3=
    {neighborhood 3 1,neighborhood 3 ModularGroup.S} := by
  rw [endRegions_eq_range,neighborhood_range]

@[expose] def infinityEnd : FiniteCuspEnds318.End 3 :=
  ⟨neighborhood 3 1,neighborhood_mem_ends 1⟩
@[expose] def zeroEnd : FiniteCuspEnds318.End 3 :=
  ⟨neighborhood 3 ModularGroup.S,neighborhood_mem_ends ModularGroup.S⟩

theorem ends_distinct : infinityEnd ≠ zeroEnd := by
  intro h
  exact ActualThreeCuspWidths318.neighborhoods_distinct (congrArg Subtype.val h)

theorem end_exhaustion (c : FiniteCuspEnds318.End 3) : c=infinityEnd ∨ c=zeroEnd := by
  have hc := c.property
  change c.val ∈ FiniteCuspEnds318.endRegions 3 at hc
  rw [endRegions_eq_pair] at hc
  rcases hc with h|h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end ActualThreeCuspExhaustion318
