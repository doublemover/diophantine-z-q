module
public import ThreeParameterCompositionOrder318
public section
noncomputable section
open Filter Topology WithTop.LinearOrderedAddCommGroup
open scoped MatrixGroups
namespace ActualThreeQOrders318
open ActualThreeQParameter318 ActualThreeQMeromorphic318 ActualThreeCuspJ318
open ThreeParameterCompositionOrder318
set_option maxHeartbeats 0

lemma qParameter_order_ne_top (g : SL(2,ℤ)) : meromorphicOrderAt (qParameter g) 0 ≠ ⊤ := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (qParameter_meromorphic g)).mpr
  exact (eventually_punctured g).mono fun q hq => qParameter_ne_zero g hq

lemma j_comp_order (g : SL(2,ℤ)) :
    meromorphicOrderAt (fun q => ThreeCompactParameter318.J (qParameter g q)) 0 =
      -(natWidth g : ℤ) := by
  rw [meromorphicOrderAt_congr ((eventually_punctured g).mono fun q hq => j_identity g hq)]
  exact j_order g

/-- The actual q-germ has either a pole of order its cusp width, or a zero
whose order times three is that width. This is an exact integer-order statement. -/
theorem qParameter_order_cases (g : SL(2,ℤ)) :
    meromorphicOrderAt (qParameter g) 0 = -(natWidth g : ℤ) ∨
      ∃ m : ℕ, 0 < m ∧ 3*m = natWidth g ∧
        meromorphicOrderAt (qParameter g) 0 = (m:ℤ) := by
  obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp (qParameter_order_ne_top g)
  have hf := qParameter_meromorphic g
  have hj := j_comp_order g
  have hw : 0 < natWidth g := RotatedWidths318.width_positive 3 (by decide) g
  rcases lt_trichotomy m 0 with hn | hz | hp
  · left
    rw [J_comp_order_of_neg hf m hm.symm hn] at hj
    exact hm.symm.trans hj
  · have h0 : meromorphicOrderAt (qParameter g) 0 = 0 := by simpa [hz] using hm.symm
    have hnon := J_comp_order_nonneg_of_zero hf h0
    rw [hj] at hnon
    have : (0:ℤ) ≤ -(natWidth g : ℤ) := by exact_mod_cast hnon
    omega
  · right
    rw [J_comp_order_of_pos hf m hm.symm hp] at hj
    have he : -3*m = -(natWidth g:ℤ) := by exact_mod_cast hj
    lift m to ℕ using hp.le with m hmNat
    refine ⟨m,by exact_mod_cast hp,?_,hm.symm⟩
    omega

/-- The actual identity cusp maps to the infinite T-cusp with simple pole.
The order-one source j-pole excludes the triple target pole at T=0. -/
theorem infinity_order : meromorphicOrderAt (qParameter 1) 0 = -1 := by
  rcases qParameter_order_cases 1 with h | ⟨m,hm,hw,ho⟩
  · simpa [natWidth,ActualThreeCuspWidths318.width_identity] using h
  · simp [natWidth,ActualThreeCuspWidths318.width_identity] at hw

/-- At the other actual cusp the rational identity alone leaves two possibilities.
Its selection is a separate global comparison obligation. -/
theorem S_order_cases : meromorphicOrderAt (qParameter ModularGroup.S) 0 = -3 ∨
    meromorphicOrderAt (qParameter ModularGroup.S) 0 = 1 := by
  rcases qParameter_order_cases ModularGroup.S with h | ⟨m,hm,hw,ho⟩
  · left
    simpa [natWidth,ActualThreeCuspWidths318.width_S] using h
  · right
    have : 3*m=3 := by simpa [natWidth,ActualThreeCuspWidths318.width_S] using hw
    have hm1 : m=1 := by omega
    simpa [hm1] using ho

@[expose] def reciprocalInfinity (q : ℂ) : ℂ := (qParameter 1 q)⁻¹

lemma reciprocalInfinity_order : meromorphicOrderAt reciprocalInfinity 0 = 1 := by
  change meromorphicOrderAt ((qParameter 1)⁻¹) 0 = _
  rw [meromorphicOrderAt_inv,infinity_order]
  norm_num

lemma reciprocalInfinity_zero : reciprocalInfinity 0 = 0 := by
  simp [reciprocalInfinity,qParameter,WidthQParameter318.punctured]

/-- The actual reciprocal infinity parameter extends analytically by zero
at the genuine source cusp origin. -/
theorem reciprocalInfinity_analytic : AnalyticAt ℂ reciprocalInfinity 0 := by
  apply AnalyticAt.of_meromorphicOrderAt_pos
  · rw [reciprocalInfinity_order]
    norm_num
  · exact reciprocalInfinity_zero

end ActualThreeQOrders318
