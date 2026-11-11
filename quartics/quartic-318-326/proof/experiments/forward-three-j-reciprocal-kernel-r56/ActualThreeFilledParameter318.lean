module
public import ActualThreeSphereCharts318
public section
noncomputable section
open Function Filter Topology
open scoped OnePoint
namespace ActualThreeFilledParameter318
open GammaOneFiber318 PeterssonQuotient318
open ActualThreeCuspFilling318 ActualThreeCuspOverlap318 ActualThreeCuspHausdorff318
open ActualThreeCuspExhaustion318 ActualThreeSphereCharts318 ActualThreeExceptionalParameter318
open FiniteCuspEnds318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The completed original parameter on the actual simultaneous cusp filling.
It retains the original map on the original quotient and the proved cusp values. -/
@[expose] def filledParameter (z : Filled) : OnePoint ℂ := by
  classical
  exact if h : ∃ b, original b=z then (quotientParameter h.choose : OnePoint ℂ)
    else if z=infinityCusp then ∞ else (0:ℂ)

lemma filledParameter_original (b : Base (image 3)) :
    filledParameter (original b) = (quotientParameter b : OnePoint ℂ) := by
  have he : ∃ a, original a=original b := ⟨b,rfl⟩
  rw [filledParameter,dite_eq_left he]
  have hb := original_openEmbedding.injective he.choose_spec
  rw [hb]

lemma filledParameter_cusp (c : End 3) : filledParameter (cusp c) = boundaryValue c := by
  have hn : ¬∃ b, original b=cusp c := by rintro ⟨b,hb⟩; exact original_ne_cusp b c hb
  rw [filledParameter,dite_eq_right hn]
  have he : cusp c=infinityCusp ↔ c=infinityEnd := by
    change cusp c=cusp infinityEnd ↔ _
    exact cusp_injective.eq_iff
  simp only [he,boundaryValue]

lemma filledParameter_disc (c : End 3) (q : disc c) :
    filledParameter (cuspChart c q) = sphereChart c q.val := by
  by_cases hq : q.val=0
  · have he : q=zeroPoint c := Subtype.ext hq
    subst q
    exact (filledParameter_cusp c).trans (sphereChart_zero c).symm
  · rw [←show original (oldMap ⟨c,⟨q.val,hq,q.property⟩⟩)=cuspChart c q from original_oldMap _,
      filledParameter_original,sphereChart_nonzero c hq]
    rw [show ActualThreeQParameter318.qParameter (representative 3 c) q.val = _ from
      ActualThreeQParameter318.qParameter_coe (representative 3 c) ⟨q.val,hq,q.property⟩]
    rfl

/-- Continuity descends through the actual open quotient map defining the
simultaneous gluing, using the actual completed q-disc functions. -/
theorem filledParameter_continuous : Continuous filledParameter := by
  let f : Base (image 3) ⊕ Discs → Filled := Sum.elim original discsMap
  have hc : Continuous f := continuous_sum_dom.mpr
    ⟨original_openEmbedding.continuous,discsMap_openEmbedding.continuous⟩
  have ho : IsOpenMap f := original_openEmbedding.isOpenMap.sumElim discsMap_openEmbedding.isOpenMap
  have hs : Surjective f := by
    intro z
    rcases TwoChartGluing318.jointly_surjective overlap z with ⟨b,hb⟩ | ⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  have hq : IsQuotientMap f := (show IsOpenQuotientMap f from ⟨hs,hc,ho⟩).isQuotientMap
  apply hq.continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · convert OnePoint.continuous_coe.comp quotientParameter_continuous using 1
    funext b
    exact filledParameter_original b
  · apply continuous_sigma
    intro c
    have hc : Continuous (fun q : disc c => sphereChart c q.val) :=
      continuousOn_iff_continuous_domRestrict.mp (sphereChart_continuousOn c)
    convert hc using 1
    funext q
    exact filledParameter_disc c q

lemma boundaryValue_injective : Injective boundaryValue := by
  intro c d he
  rcases end_exhaustion c with rfl | rfl <;> rcases end_exhaustion d with rfl | rfl
  · rfl
  · rw [boundary_infinity,boundary_zero] at he
    exact (OnePoint.infty_ne_coe 0 he).elim
  · rw [boundary_zero,boundary_infinity] at he
    exact (OnePoint.coe_ne_infty 0 he).elim
  · rfl

lemma original_value_ne_boundary (b : Base (image 3)) (c : End 3) :
    (quotientParameter b : OnePoint ℂ) ≠ boundaryValue c := by
  rcases end_exhaustion c with rfl | rfl
  · rw [boundary_infinity]
    exact OnePoint.coe_ne_infty _
  · rw [boundary_zero]
    exact fun h => quotientParameter_ne_zero b (OnePoint.coe_injective h)

/-- The original global injectivity and the exact two distinct boundary values
prove injectivity of this same completed map on the actual filling. -/
theorem filledParameter_injective : Injective filledParameter := by
  intro x y he
  rcases original_or_cusp x with ⟨b,rfl⟩ | ⟨c,rfl⟩ <;>
    rcases original_or_cusp y with ⟨d,rfl⟩ | ⟨e,rfl⟩
  · rw [filledParameter_original,filledParameter_original] at he
    have hb := ActualThreeGlobalParameter318.fullParameter_injective
      (Subtype.ext (OnePoint.coe_injective he))
    exact congrArg original hb
  · rw [filledParameter_original,filledParameter_cusp] at he
    exact (original_value_ne_boundary b e he).elim
  · rw [filledParameter_cusp,filledParameter_original] at he
    exact (original_value_ne_boundary d c he.symm).elim
  · rw [filledParameter_cusp,filledParameter_cusp] at he
    exact congrArg cusp (boundaryValue_injective he)

/-- Every point of the independent standard sphere is attained by the same
completed map, including the two boundary points. -/
theorem filledParameter_surjective : Surjective filledParameter := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨infinityCusp,(filledParameter_cusp infinityEnd).trans boundary_infinity⟩
  | coe t =>
    by_cases ht : t=0
    · subst t
      exact ⟨zeroCusp,(filledParameter_cusp zeroEnd).trans boundary_zero⟩
    · obtain ⟨b,hb⟩ := ActualThreeParameterProper318.fullParameter_surjective ⟨t,ht⟩
      exact ⟨original b,(filledParameter_original b).trans
        (congrArg (fun w : ℂ => (w : OnePoint ℂ)) (congrArg Subtype.val hb))⟩

/-- The actual compactified Gamma1(3) quotient is homeomorphic to the independent
standard one-point compactification of C, by the original period T itself. -/
@[expose] def compactHomeomorph : Filled ≃ₜ OnePoint ℂ := by
  letI := ActualThreeCuspCompact318.filled_compactSpace
  exact (Equiv.ofBijective filledParameter ⟨filledParameter_injective,filledParameter_surjective⟩).toHomeomorphOfContinuousClosed
    filledParameter_continuous filledParameter_continuous.isClosedMap

lemma compactHomeomorph_apply (z : Filled) : compactHomeomorph z = filledParameter z := rfl

lemma compactHomeomorph_original (b : Base (image 3)) :
    compactHomeomorph (original b) = (quotientParameter b : OnePoint ℂ) :=
  filledParameter_original b

lemma compactHomeomorph_infinity : compactHomeomorph infinityCusp = ∞ :=
  (filledParameter_cusp infinityEnd).trans boundary_infinity

lemma compactHomeomorph_zero : compactHomeomorph zeroCusp = (0:ℂ) :=
  (filledParameter_cusp zeroEnd).trans boundary_zero

end ActualThreeFilledParameter318
