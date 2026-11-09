module
public import ActualThreeParameterProper318
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
namespace ActualThreeGlobalParameter318
open ActualThreeExceptionalParameter318 ActualThreeParameterProper318 ThreeCompactParameter318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
set_option maxHeartbeats 0

/-- A Hausdorff source open map that is injective over a dense target subset
is globally injective. Openness is essential; properness alone would not suffice. -/
lemma injective_of_open_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} {A : Set Y} (ho : IsOpenMap f) (hd : Dense A)
    (hi : ∀ x y, f x=f y → f x ∈ A → x=y) : Function.Injective f := by
  intro x y hxy
  by_contra hn
  obtain ⟨U,V,hU,hV,hx,hy,huv⟩ := t2_separation hn
  have he : (f '' U ∩ f '' V).Nonempty := ⟨f x,⟨x,hx,rfl⟩,⟨y,hy,hxy.symm⟩⟩
  obtain ⟨z,⟨⟨u,hu,huz⟩,⟨v,hv,hvz⟩⟩,hz⟩ :=
    hd.inter_open_nonempty _ ((ho U hU).inter (ho V hV)) he
  have huv' := hi u v (huz.trans hvz.symm) (huz.symm ▸ hz)
  exact Set.disjoint_left.mp huv hu (huv'.symm ▸ hv)

/-- Complex open mapping is applied to the actual globally analytic period
coordinate on H. Its already proved surjectivity to C* rules out constancy. -/
theorem periodParameter_isOpenMap : IsOpenMap periodParameter := by
  let f : ℂ → ℂ := fun z => periodParameter (UpperHalfPlane.ofComplex z)
  have ha : AnalyticOnNhd ℂ f {z : ℂ | 0<z.im} := by
    intro z hz
    exact periodParameter_analyticAt ⟨z,hz⟩
  have hc : IsPreconnected {z : ℂ | 0<z.im} :=
    (Complex.isConnected_of_upperHalfPlane Set.Subset.rfl (by grind)).isPreconnected
  obtain ⟨w,hw⟩ | ho := ha.is_constant_or_isOpen hc
  · obtain ⟨tau,htau⟩ := periodParameter_surjective 1 (by norm_num)
    obtain ⟨sigma,hsigma⟩ := periodParameter_surjective 2 (by norm_num)
    have ht := hw (tau:ℂ) tau.im_pos
    have hs := hw (sigma:ℂ) sigma.im_pos
    simp only [f,UpperHalfPlane.ofComplex_apply,htau,hsigma] at ht hs
    norm_num [←ht] at hs
  · intro U hU
    have he : f '' ((fun tau : UpperHalfPlane => (tau:ℂ)) '' U)=periodParameter '' U := by
      ext z
      constructor
      · rintro ⟨_,⟨tau,htau,rfl⟩,rfl⟩
        exact ⟨tau,htau,by simp [f]⟩
      · rintro ⟨tau,htau,rfl⟩
        exact ⟨tau,⟨tau,htau,rfl⟩,by simp [f]⟩
    rw [←he]
    apply ho
    · rintro z ⟨tau,htau,rfl⟩
      exact tau.im_pos
    · exact UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU

/-- Openness descends through the genuine orbit projection, without imposing
any new quotient topology or assuming a complex atlas at elliptic points. -/
theorem quotientParameter_isOpenMap : IsOpenMap quotientParameter := by
  intro U hU
  have he : periodParameter '' ((quotientMap 3) ⁻¹' U)=quotientParameter '' U := by
    ext z
    constructor
    · rintro ⟨tau,htau,rfl⟩
      exact ⟨quotientMap 3 tau,htau,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      obtain ⟨tau,rfl⟩ := quotient_surjective 3 q
      exact ⟨tau,hq,rfl⟩
  rw [←he]
  apply periodParameter_isOpenMap
  exact (continuous_quot_mk).isOpen_preimage U hU

theorem fullParameter_isOpenMap : IsOpenMap fullParameter := by
  intro U hU
  have he : fullParameter '' U=Subtype.val ⁻¹' (quotientParameter '' U) := by
    ext t
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,hqt⟩
      exact ⟨q,hq,Subtype.ext hqt⟩
  rw [he]
  exact continuous_subtype_val.isOpen_preimage _ (quotientParameter_isOpenMap U hU)

lemma injective_over_admissible (x y : Base (image 3))
    (he : fullParameter x=fullParameter y)
    (hx : (fullParameter x).val+27 ≠ 0 ∧ (fullParameter x).val+243 ≠ 0 ∧
      D (fullParameter x).val ≠ 0) : x=y := by
  have hjx : QuotientJ318.jMap 3 x ≠ 0 ∧ QuotientJ318.jMap 3 x ≠ 1728 := by
    rw [←quotientParameter_j]
    exact ⟨(J_ne_zero_iff (quotientParameter_ne_zero x)).mpr ⟨hx.1,hx.2.1⟩,
      (J_ne_1728_iff (quotientParameter_ne_zero x)).mpr hx.2.2⟩
  have hjxy : QuotientJ318.jMap 3 x=QuotientJ318.jMap 3 y := by
    rw [←quotientParameter_j,←quotientParameter_j]
    exact congrArg (fun t : NonzeroParameter => J t.val) he
  have hjy : QuotientJ318.jMap 3 y ≠ 0 ∧ QuotientJ318.jMap 3 y ≠ 1728 := hjxy ▸ hjx
  let a : ThreeArithmeticQuotient318.Source := ⟨x,hjx⟩
  let b : ThreeArithmeticQuotient318.Source := ⟨y,hjy⟩
  have hab : LiteralThreeCompactParameter318.sourceParameter 1 a=
      LiteralThreeCompactParameter318.sourceParameter 1 b := by
    apply Subtype.ext
    rw [←quotientParameter_restrict 1 a,←quotientParameter_restrict 1 b]
    exact congrArg Subtype.val he
  exact congrArg Subtype.val ((LiteralThreeCompactParameter318.sourceParameter 1).injective hab)

/-- Actual global injectivity includes both formerly excluded elliptic fibers. -/
theorem fullParameter_injective : Function.Injective fullParameter :=
  injective_of_open_dense fullParameter_isOpenMap admissible_dense injective_over_admissible

/-- The actual entire Gamma1(3) orbit quotient is homeomorphic to the punctured
complex line by the explicit period parameter. This is not yet a compactified
source biholomorphism or a quotient complex-atlas theorem. -/
@[expose] def globalHomeomorph : Base (image 3) ≃ₜ NonzeroParameter :=
  (Equiv.ofBijective fullParameter ⟨fullParameter_injective,fullParameter_surjective⟩).toHomeomorphOfContinuousOpen fullParameter_continuous fullParameter_isOpenMap

@[simp] theorem globalHomeomorph_apply (q : Base (image 3)) :
    globalHomeomorph q=fullParameter q := rfl

theorem globalHomeomorph_j (q : Base (image 3)) :
    J (globalHomeomorph q).val=QuotientJ318.jMap 3 q := quotientParameter_j q

theorem globalHomeomorph_inverse_j (t : NonzeroParameter) :
    QuotientJ318.jMap 3 (globalHomeomorph.symm t)=J t.val := by
  rw [←globalHomeomorph_j,globalHomeomorph.apply_symm_apply]

/-- Complete actual exceptional zero fiber in the global coordinate. -/
theorem j_zero_parameter_iff (q : Base (image 3)) :
    QuotientJ318.jMap 3 q=0 ↔
      (globalHomeomorph q).val = -27 ∨ (globalHomeomorph q).val = -243 := by
  rw [←globalHomeomorph_j]
  simpa only [not_and_or,not_ne_iff,add_eq_zero_iff_eq_neg] using
    not_congr (J_ne_zero_iff (globalHomeomorph q).property)

/-- Every actual point above 1728 corresponds to exactly a root of D;
no generic-fiber argument discards an exceptional orbit. -/
theorem j_1728_parameter_iff (q : Base (image 3)) :
    QuotientJ318.jMap 3 q=1728 ↔ D (globalHomeomorph q).val=0 := by
  rw [←globalHomeomorph_j]
  simpa only [not_ne_iff] using
    not_congr (J_ne_1728_iff (globalHomeomorph q).property)

@[expose] def zeroSimplePoint : Base (image 3) :=
  globalHomeomorph.symm ⟨-27,by norm_num⟩
@[expose] def zeroTriplePoint : Base (image 3) :=
  globalHomeomorph.symm ⟨-243,by norm_num⟩

theorem zero_points_distinct : zeroSimplePoint ≠ zeroTriplePoint := by
  intro h
  have hh := congrArg (fun q => (globalHomeomorph q).val) h
  norm_num [zeroSimplePoint,zeroTriplePoint] at hh

/-- Exactly two distinct actual quotient points lie over zero. Their names
refer only to the independently computed rational target J orders; no new
source complex atlas or source ramification-order statement is asserted. -/
theorem j_zero_iff (q : Base (image 3)) :
    QuotientJ318.jMap 3 q=0 ↔ q=zeroSimplePoint ∨ q=zeroTriplePoint := by
  rw [j_zero_parameter_iff]
  constructor
  · rintro (h|h)
    · left
      apply globalHomeomorph.injective
      apply Subtype.ext
      simpa [zeroSimplePoint] using h
    · right
      apply globalHomeomorph.injective
      apply Subtype.ext
      simpa [zeroTriplePoint] using h
  · rintro (rfl|rfl)
    · left; simp [zeroSimplePoint]
    · right; simp [zeroTriplePoint]

end ActualThreeGlobalParameter318
