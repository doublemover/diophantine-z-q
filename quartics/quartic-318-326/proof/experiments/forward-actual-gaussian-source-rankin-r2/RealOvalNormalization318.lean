module
public import RealQuarticGroup318
public section
noncomputable section

/-! Actual additive and topological normalization of the entire real oval. -/
namespace RealOvalNormalization318
open RealQuarticGroup318 ReciprocalGroup318
set_option maxHeartbeats 1000000

variable (D : ℝ) (hD : 0<D) (r : ℝ) (hr : 0<r) (hpow : r^4=D)
local instance targetGroup : AddCommGroup (Oval 1) := group 1 (by norm_num)

@[expose] def forward (p : Oval D) : Oval 1 :=
  ⟨(r*p.val.1,p.val.2),by
    change p.val.2^2=1-(1:ℝ)*(r*p.val.1)^4
    rw [one_mul,mul_pow,hpow]
    exact p.property⟩

@[expose] def backward (p : Oval 1) : Oval D :=
  ⟨(p.val.1/r,p.val.2),by
    change p.val.2^2=1-D*(p.val.1/r)^4
    have he : D*(p.val.1/r)^4=p.val.1^4 := by
      rw [←hpow]
      field_simp [hr.ne']
    rw [he]
    simpa only [one_mul] using p.property⟩

@[expose] def ovalEquiv : Oval D ≃ Oval 1 where
  toFun := forward D r hpow
  invFun := backward D r hr hpow
  left_inv p := by apply Subtype.ext; simp [forward,backward,hr.ne']
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change r*(p.val.1/r)=p.val.1
      field_simp [hr.ne']
    · rfl

include hpow in
lemma denominator (u a : ℝ) :
    1+(1:ℝ)*(r*u)^2*(r*a)^2=1+D*u^2*a^2 := by rw [←hpow]; ring

include hpow in
lemma sumU_normalized (u v a b : ℝ) :
    sumU 1 (r*u) v (r*a) b=r*sumU D u v a b := by
  unfold sumU
  rw [denominator D r hpow,←mul_div_assoc]
  congr 1
  ring

include hpow in
lemma sumV_normalized (u v a b : ℝ) :
    sumV 1 (r*u) v (r*a) b=sumV D u v a b := by
  unfold sumV
  rw [denominator D r hpow]
  congr 1
  rw [←hpow]
  ring

lemma forward_add (p q : Oval D) :
    letI : AddCommGroup (Oval D) := group D hD
    forward D r hpow (p+q)=forward D r hpow p+forward D r hpow q := by
  letI : AddCommGroup (Oval D) := group D hD
  apply Subtype.ext
  apply Prod.ext
  · exact (sumU_normalized D r hpow p.val.1 p.val.2 q.val.1 q.val.2).symm
  · exact (sumV_normalized D r hpow p.val.1 p.val.2 q.val.1 q.val.2).symm

/-- The full oval group, including v=0 and both u=0 points, is normalized. -/
@[expose] def ovalAddEquiv :
    letI : AddCommGroup (Oval D) := group D hD
    Oval D ≃+ Oval 1 := by
  letI : AddCommGroup (Oval D) := group D hD
  exact { ovalEquiv D r hr hpow with map_add' := forward_add D hD r hpow }

lemma forward_continuous : Continuous (forward D r hpow) := by
  unfold forward
  fun_prop

lemma backward_continuous : Continuous (backward D r hr hpow) := by
  unfold backward
  fun_prop

@[expose] def ovalHomeomorph : Oval D ≃ₜ Oval 1 :=
  { ovalEquiv D r hr hpow with
    continuous_toFun := forward_continuous D r hpow
    continuous_invFun := backward_continuous D r hr hpow }

/-- The existing analytic parametrization gives actual connectedness of the
whole oval without asserting that this parametrization is additive. -/
@[expose] def cover (t : ℝ) : Oval D :=
  ⟨(RealQuarticOvalCover318.u D t,RealQuarticOvalCover318.v t),
    RealQuarticOvalCover318.oval_equation hD t⟩

lemma cover_continuous : Continuous (cover D hD) := by
  unfold cover RealQuarticOvalCover318.u RealQuarticOvalCover318.v
  fun_prop

lemma cover_surjective : Function.Surjective (cover D hD) := by
  intro p
  obtain ⟨t,hu,hv⟩ := RealQuarticOvalCover318.oval_surjective hD p.val.1 p.val.2 p.property
  refine ⟨t,?_⟩
  apply Subtype.ext
  exact Prod.ext hu hv

include hD in
theorem oval_connected : ConnectedSpace (Oval D) :=
  (cover_surjective D hD).connectedSpace (cover_continuous D hD)

end RealOvalNormalization318
