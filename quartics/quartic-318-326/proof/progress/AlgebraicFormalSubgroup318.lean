module
public import FormalChartGroup318
public import FormalChartDouble
public section
namespace AlgebraicFormalSubgroup318
open ReciprocalDouble318 FormalChordAlgebra318 FormalChartGroup318 WeierstrassCurve.Affine
variable {F:Type*} [Field F] [CharZero F] [DecidableEq F]
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma ne_zero_of_unit (w:AbsoluteValue F ℝ) (a:F) (ha:w a=1) : a≠0 := by
  intro he
  simpa [he] using ha

lemma secant_pole (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D x₁ y₁ x₂ y₂:F) (hD:w D≤1)
    (h₁:(E D).Nonsingular x₁ y₁) (h₂:(E D).Nonsingular x₂ y₂)
    (hx₁:1<w x₁) (hx₂:1<w x₂) (hx:x₁≠x₂) :
    1<w ((Point.some x₁ y₁ h₁+Point.some x₂ y₂ h₂).xRep 0) := by
  obtain ⟨hy₁,_,hz₁s,ht₁s,hc₁⟩:=FormalChartNorm.affine_to_small_chart w hna D x₁ y₁ hD hx₁
    (FormalChartDouble.ordinate_equation D x₁ y₁ h₁)
  obtain ⟨hy₂,_,hz₂s,ht₂s,hc₂⟩:=FormalChartNorm.affine_to_small_chart w hna D x₂ y₂ hD hx₂
    (FormalChartDouble.ordinate_equation D x₂ y₂ h₂)
  let z₁:= -x₁/y₁
  let t₁:= -1/y₁
  let z₂:= -x₂/y₂
  let t₂:= -1/y₂
  have ht₁:t₁≠0:=div_ne_zero (by norm_num) hy₁
  have ht₂:t₂≠0:=div_ne_zero (by norm_num) hy₂
  have hxx₁:z₁/t₁=x₁ := by dsimp [z₁,t₁]; field_simp [hy₁]
  have hyy₁:-1/t₁=y₁ := by dsimp [t₁]; field_simp [hy₁]
  have hxx₂:z₂/t₂=x₂ := by dsimp [z₂,t₂]; field_simp [hy₂]
  have hyy₂:-1/t₂=y₂ := by dsimp [t₂]; field_simp [hy₂]
  obtain ⟨hdunit,_,_,hqunit,hz₃s,ht₃s⟩:=FormalChartNorm.chord_small w hna D z₁ t₁ z₂ t₂ hD hz₁s ht₁s hz₂s ht₂s
  have hd:=ne_zero_of_unit w _ hdunit
  have hq:1-D*(lambda D z₁ t₁ z₂ t₂)^2≠0:=ne_zero_of_unit w _ hqunit
  have hx':z₁/t₁≠z₂/t₂ := by simpa only [hxx₁,hxx₂] using hx
  have hz:z₁≠z₂ := by
    intro he
    have hdif:=difference D z₁ t₁ z₂ t₂ hc₁ hc₂ hd
    rw [he,sub_self,mul_zero] at hdif
    have ht:t₁=t₂:=sub_eq_zero.mp hdif
    exact hx' (by rw [he,ht])
  have hn₁:(E D).Nonsingular (z₁/t₁) (-1/t₁) := by simpa only [hxx₁,hyy₁] using h₁
  have hn₂:(E D).Nonsingular (z₂/t₂) (-1/t₂) := by simpa only [hxx₂,hyy₂] using h₂
  obtain ⟨ht₃,hz₃,hn₃,hadd⟩:=actual_secant D z₁ t₁ z₂ t₂ hc₁ hc₂ ht₁ ht₂ hd hz hx' hn₁ hn₂ hq
  simp only [hxx₁,hyy₁,hxx₂,hyy₂] at hadd
  rw [hadd]
  simp only [Point.xRep_some,Matrix.cons_val_zero]
  apply FormalChartNorm.small_chart_to_pole w hna D _ _ hD hz₃ ht₃ hz₃s ht₃s
  have hl₁:=line_one D z₁ t₁ z₂ t₂
  have hl₂:=line_two D z₁ t₁ z₂ t₂ hc₁ hc₂ hd
  apply third_curve D _ _ z₁ z₂ hz hq
  · rw [←hl₁]; exact hc₁
  · rw [←hl₂]; exact hc₂

/-- The formal neighbourhood of infinity is an actual subgroup for every
nonarchimedean absolute value and integral short model. Residue2 is included. -/
@[expose] def formalSubgroup (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D:F) (hD:w D≤1) : AddSubgroup (E D).Point where
  carrier := {Q | Q=0 ∨ 1<w (Q.xRep 0)}
  zero_mem' := Or.inl rfl
  neg_mem' := by
    intro Q hQ
    rcases hQ with rfl|hx
    · exact Or.inl (neg_zero)
    · right
      simpa only [Point.xRep_neg] using hx
  add_mem' := by
    intro Q R hQ hR
    change Q+R=0 ∨ 1<w ((Q+R).xRep 0)
    change Q=0 ∨ 1<w (Q.xRep 0) at hQ
    change R=0 ∨ 1<w (R.xRep 0) at hR
    rcases hQ with rfl|hQ
    · simpa only [zero_add] using hR
    rcases hR with rfl|hR
    · simpa only [add_zero] using (Or.inr hQ : Q=0 ∨ 1<w (Q.xRep 0))
    cases Q with
    | zero =>
      left
      exfalso
      change 1<w ((0:(E D).Point).xRep 0) at hQ
      simpa only [Point.xRep_zero,Matrix.cons_val_zero,map_one,lt_self_iff_false] using hQ
    | some x₁ y₁ hn₁ =>
      cases R with
      | zero =>
        left
        exfalso
        change 1<w ((0:(E D).Point).xRep 0) at hR
        simpa only [Point.xRep_zero,Matrix.cons_val_zero,map_one,lt_self_iff_false] using hR
      | some x₂ y₂ hn₂ =>
        by_cases hx:x₁=x₂
        · rcases Point.X_eq_iff.mp hx with he|he
          · right
            rw [he]
            exact FormalChartDouble.point_double_pole w hna D _ hD hR
          · left
            rw [he,neg_add_cancel]
        · right
          exact secant_pole w hna D x₁ y₁ x₂ y₂ hD hn₁ hn₂ hQ hR hx

@[simp] theorem mem_formalSubgroup (w:AbsoluteValue F ℝ) (hna:IsNonarchimedean w)
    (D:F) (hD:w D≤1) (Q:(E D).Point) :
    Q∈formalSubgroup w hna D hD ↔ Q=0 ∨ 1<w (Q.xRep 0) := Iff.rfl

#print axioms secant_pole
#print axioms formalSubgroup
end
end AlgebraicFormalSubgroup318
