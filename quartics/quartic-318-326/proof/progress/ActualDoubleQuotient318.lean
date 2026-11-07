module
public import ActualChord318
public import Mathlib.GroupTheory.Index
public section
namespace ActualDoubleQuotient318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalNormCoset318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
noncomputable section

@[expose] def affineCode (x y:K) (h:E.Nonsingular x y) (hx:x≠0) : Fin 8 :=
  Classical.choose (GlobalFirstDescent318.first_descent_classes x y h hx)

theorem affineCode_spec (x y:K) (h:E.Nonsingular x y) (hx:x≠0) :
    ∃r:K,r≠0 ∧ x=classRepresentative (affineCode x y h hx)*r^2 :=
  Classical.choose_spec (GlobalFirstDescent318.first_descent_classes x y h hx)

@[expose] def pointCode : E.Point → Fin 10
  | .zero=>0
  | .some x y h=>if hx:x=0 then 1 else
      ⟨(affineCode x y h hx).val+2,by have hh:=(affineCode x y h hx).isLt; omega⟩

theorem zero_x_point (x y:K) (h:E.Nonsingular x y) (hx:x=0) : Point.some x y h=T 0 := by
  subst x
  have he:=h.1
  rw [equation_iff] at he
  have hy:y=0 := by
    have hy2:y^2=0 := by simpa [E] using he
    exact mul_self_eq_zero.mp (by simpa only [pow_two] using hy2)
  subst y
  rfl

theorem affine_same_code (x₁ x₂ y₁ y₂:K) (h₁:E.Nonsingular x₁ y₁) (h₂:E.Nonsingular x₂ y₂)
    (hx₁:x₁≠0) (hx₂:x₂≠0) (hc:affineCode x₁ y₁ h₁ hx₁=affineCode x₂ y₂ h₂ hx₂) :
    ∃Q:E.Point,Q+Q=Point.some x₁ y₁ h₁-Point.some x₂ y₂ h₂ := by
  obtain ⟨r,hr,he₁⟩:=affineCode_spec x₁ y₁ h₁ hx₁
  obtain ⟨s,hs,he₂⟩:=affineCode_spec x₂ y₂ h₂ hx₂
  rw [←hc] at he₂
  let c:=classRepresentative (affineCode x₁ y₁ h₁ hx₁)
  have hprod:x₁*x₂=(c*r*s)^2 := by rw [he₁,he₂]; dsimp [c]; ring
  have hcs:c*r*s≠0 := by intro hh; rw [hh,zero_pow (by decide)] at hprod; exact (mul_ne_zero hx₁ hx₂) hprod
  exact ActualChord318.square_product_difference_double x₁ x₂ y₁ y₂ _ hcs hprod h₁ h₂

theorem same_code_difference_double (P Q:E.Point) (hc:pointCode P=pointCode Q) :
    ∃U:E.Point,U+U=P-Q := by
  cases P with
  | zero =>
    cases Q with
    | zero => exact ⟨0,by simp⟩
    | some x y h =>
      have hh:=congrArg Fin.val hc
      by_cases hx:x=0 <;> simp [pointCode,hx] at hh
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      have hh:=congrArg Fin.val hc
      by_cases hx:x₁=0 <;> simp [pointCode,hx] at hh
    | some x₂ y₂ h₂ =>
      have hh:=congrArg Fin.val hc
      by_cases hx₁:x₁=0
      · by_cases hx₂:x₂=0
        · exact ⟨0,by rw [zero_x_point x₁ y₁ h₁ hx₁,zero_x_point x₂ y₂ h₂ hx₂]; simp⟩
        · simp [pointCode,hx₁,hx₂] at hh
      · by_cases hx₂:x₂=0
        · simp [pointCode,hx₁,hx₂] at hh
        · simp only [pointCode,dif_neg hx₁,dif_neg hx₂] at hh
          have hc':affineCode x₁ y₁ h₁ hx₁=affineCode x₂ y₂ h₂ hx₂ := by
            apply Fin.ext
            omega
          exact affine_same_code x₁ x₂ y₁ y₂ h₁ h₂ hx₁ hx₂ hc'

@[expose] abbrev doubles : AddSubgroup E.Point := (nsmulAddMonoidHom (α:=E.Point) 2).range
@[expose] abbrev DoubleQuotient := E.Point ⧸ doubles
@[expose] def quotientCode (q:DoubleQuotient) : Fin 10 := pointCode q.out

theorem quotientCode_injective : Function.Injective quotientCode := by
  intro a b hab
  obtain ⟨Q,hQ⟩:=same_code_difference_double a.out b.out hab
  have hm:a.out-b.out∈doubles := by
    refine ⟨Q,?_⟩
    simpa only [nsmulAddMonoidHom_apply,two_nsmul] using hQ
  have he:(a.out:DoubleQuotient)=(b.out:DoubleQuotient) := QuotientAddGroup.eq_iff_sub_mem.mpr hm
  change Quotient.mk'' a.out=Quotient.mk'' b.out at he
  simpa only [Quotient.out_eq'] using he

instance doubleQuotient_finite : Finite DoubleQuotient := Finite.of_injective quotientCode quotientCode_injective

theorem double_quotient_card_le_ten : Nat.card DoubleQuotient≤10 := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective quotientCode quotientCode_injective

theorem doubles_finiteIndex : doubles.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient

end
end ActualDoubleQuotient318
#print axioms ActualDoubleQuotient318.same_code_difference_double
