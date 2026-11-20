module
public import ActualTwoDescentEllipticModel318
public import OriginalRCMilneProjectiveTwist318
public import OriginalRCMilneSplitLocal318
import all ActualTwoDescentEllipticModel318

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
noncomputable section

namespace OriginalRCMilneTwistPointGroup318

open WeierstrassCurve.Affine ActualTwoDescentEllipticModel318
open OriginalRCMilneProjectiveTwist318

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private theorem scaled_affine_eq (r n s x y : F) (hn : n=s^2*r)
    (hy : y^2=x*(x-r)*(x+3*r)) :
    (s^3*y)^2=(s^2*x)*(s^2*x-n)*(s^2*x+3*n) := by
  have he := scaled_equation r (s^2) s x y 1 rfl
  rw [← hn] at he
  simp only [equation,mul_one,hy,sub_self,mul_zero] at he
  exact sub_eq_zero.mp he

/-- The forward map on the original elliptic point type, not a bijection
between untyped coordinates. The same root fixes the origin. -/
def scalePoint (r n s : F) (hn : n ≠ 0) (hc : n=s^2*r) :
    Point r → Point n
  | .zero => .zero
  | .some x y H => point n (s^2*x) (s^3*y) hn
      (scaled_affine_eq r n s x y hc ((curve_equation r x y).mp H.1))

private theorem vertical_iff (r n s x₁ x₂ y₁ y₂ : F) (hs : s ≠ 0) :
    (s^2*x₁=s^2*x₂ ∧ s^3*y₁=(curve n).toAffine.negY (s^2*x₂) (s^3*y₂)) ↔
      (x₁=x₂ ∧ y₁=(curve r).toAffine.negY x₂ y₂) := by
  simp only [curve_negY,←mul_neg]
  constructor
  · intro h
    exact ⟨mul_left_cancel₀ (pow_ne_zero _ hs) h.1,
      mul_left_cancel₀ (pow_ne_zero _ hs) h.2⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨congrArg (fun z : F => s^2*z) h₁,congrArg (fun z : F => s^3*z) h₂⟩

theorem scaleSlope (r n s x₁ x₂ y₁ y₂ : F) (hs : s ≠ 0) (hn : n=s^2*r)
    (H₁ : (curve r).toAffine.Equation x₁ y₁)
    (H₂ : (curve r).toAffine.Equation x₂ y₂)
    (h : ¬(x₁=x₂ ∧ y₁=(curve r).toAffine.negY x₂ y₂)) :
    (curve n).toAffine.slope (s^2*x₁) (s^2*x₂) (s^3*y₁) (s^3*y₂) =
      s*(curve r).toAffine.slope x₁ x₂ y₁ y₂ := by
  have h' := fun p => h ((vertical_iff r n s x₁ x₂ y₁ y₂ hs).mp p)
  by_cases hx : x₁=x₂
  · have hx' : s^2*x₁=s^2*x₂ := congrArg (fun z : F => s^2*z) hx
    have hy : y₁ ≠ (curve r).toAffine.negY x₂ y₂ := fun p => h ⟨hx,p⟩
    have hy' : s^3*y₁ ≠ (curve n).toAffine.negY (s^2*x₂) (s^3*y₂) :=
      fun p => h' ⟨hx',p⟩
    have hyEq : y₁=y₂ := Y_eq_of_Y_ne H₁ H₂ hx hy
    have hsum : y₁+y₁ ≠ 0 := by
      intro h0
      apply hy
      rw [curve_negY,←hyEq]
      have h₀ := congrArg (fun z : F => z-y₁) h0
      simpa only [add_sub_cancel_right,zero_sub] using h₀
    rw [slope_of_Y_ne hx' hy',slope_of_Y_ne hx hy]
    simp only [curve_negY,sub_neg_eq_add,WeierstrassCurve.toAffine,curve,
      zero_mul,sub_zero]
    have hd : s^3*y₁+s^3*y₁ = s^3*(y₁+y₁) := by ring
    rw [hd,hn]
    field_simp [hs,hsum] <;> ring
  · have hx' : s^2*x₁≠s^2*x₂ :=
      fun p => hx (mul_left_cancel₀ (pow_ne_zero _ hs) p)
    have hy : s^3*y₁-s^3*y₂ = s^3*(y₁-y₂) := by ring
    have hd : s^2*x₁-s^2*x₂ = s^2*(x₁-x₂) := by ring
    rw [slope_of_X_ne hx',slope_of_X_ne hx,hy,hd]
    field_simp [hs,sub_ne_zero.mpr hx] <;> ring

theorem scaleAddX (r n s x₁ x₂ lam : F) (hn : n=s^2*r) :
    (curve n).toAffine.addX (s^2*x₁) (s^2*x₂) (s*lam) =
      s^2*(curve r).toAffine.addX x₁ x₂ lam := by
  simp only [addX,WeierstrassCurve.toAffine,curve,hn]
  ring

theorem scaleAddY (r n s x₁ x₂ y₁ lam : F) (hn : n=s^2*r) :
    (curve n).toAffine.addY (s^2*x₁) (s^2*x₂) (s^3*y₁) (s*lam) =
      s^3*(curve r).toAffine.addY x₁ x₂ y₁ lam := by
  simp only [addY,curve_negY,negAddY,scaleAddX r n s x₁ x₂ lam hn]
  ring

/-- The same coordinate map respects the actual elliptic group law in all
branches, including infinity, vertical, secant, and tangent. -/
theorem scalePoint_add (r n s : F) (hn : n ≠ 0) (hs : s ≠ 0) (hc : n=s^2*r)
    (P Q : Point r) :
    scalePoint r n s hn hc (P+Q)=scalePoint r n s hn hc P+scalePoint r n s hn hc Q := by
  cases P with
  | zero => cases Q <;> rfl
  | some x₁ y₁ H₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ H₂ =>
      have hcmp := vertical_iff r n s x₁ x₂ y₁ y₂ hs
      by_cases h : x₁=x₂ ∧ y₁=(curve r).toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq h.1 h.2]
        dsimp only [scalePoint,point]
        have p := hcmp.mpr h
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq p.1 p.2]
      · have h' := fun p => h (hcmp.mp p)
        rw [WeierstrassCurve.Affine.Point.add_some h]
        dsimp only [scalePoint,point]
        rw [WeierstrassCurve.Affine.Point.add_some h']
        congr 1
        · rw [scaleSlope r n s x₁ x₂ y₁ y₂ hs hc H₁.1 H₂.1 h,
            scaleAddX r n s x₁ x₂ _ hc]
        · rw [scaleSlope r n s x₁ x₂ y₁ y₂ hs hc H₁.1 H₂.1 h,
            scaleAddY r n s x₁ x₂ y₁ _ hc]

private theorem inverse_parameter (r n s : F) (hs : s ≠ 0) (hc : n=s^2*r) :
    r=(s⁻¹)^2*n := by
  rw [hc]
  field_simp [hs] <;> ring

private theorem scale_inv_times (s x : F) (j : ℕ) (hs : s ≠ 0) :
    (s⁻¹)^j*(s^j*x)=x := by
  rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ hs,one_pow,one_mul]

/-- The genuine pointed change of variables is an additive equivalence;
its inverse is the literal scale by the reciprocal of the same root. -/
def twistAddEquiv (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0) (hs : s ≠ 0) (hc : n=s^2*r) :
    Point r ≃+ Point n where
  toFun := scalePoint r n s hn hc
  invFun := scalePoint n r s⁻¹ hr (inverse_parameter r n s hs hc)
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y H =>
      simp only [scalePoint,point,WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨scale_inv_times s x 2 hs,scale_inv_times s y 3 hs⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y H =>
      simp only [scalePoint,point,WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨by simpa only [inv_inv] using scale_inv_times s⁻¹ x 2 (inv_ne_zero hs),
        by simpa only [inv_inv] using scale_inv_times s⁻¹ y 3 (inv_ne_zero hs)⟩
  map_add' := scalePoint_add r n s hn hs hc

theorem twistAddEquiv_apply (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : s ≠ 0) (hc : n=s^2*r) (P : Point r) :
    twistAddEquiv r n s hr hn hs hc P = scalePoint r n s hn hc P := rfl

/-- Apply to the actual ordered chart of the Weil restriction. The second
factor is literally the chosen-root twist, not a reselected isomorphism. -/
def splitPhi (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0) (hs : s ≠ 0) (hc : n=s^2*r) :
    Point r × Point r →+ Point r × Point n where
  toFun p := (p.1+p.2, twistAddEquiv r n s hr hn hs hc (p.1-p.2))
  map_zero' := by apply Prod.ext <;> simp
  map_add' p q := by
    apply Prod.ext
    · change (p.1+q.1)+(p.2+q.2)=(p.1+p.2)+(q.1+q.2)
      abel
    · change twistAddEquiv r n s hr hn hs hc ((p.1+q.1)-(p.2+q.2)) =
        twistAddEquiv r n s hr hn hs hc (p.1-p.2)+twistAddEquiv r n s hr hn hs hc (q.1-q.2)
      rw [←map_add]
      apply congrArg (twistAddEquiv r n s hr hn hs hc)
      abel

/-- Literal point comparison needed before the split kernel/cokernel read. -/
theorem splitPhi_normalized (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : s ≠ 0) (hc : n=s^2*r) (P : Point r × Point r) :
    ((splitPhi r n s hr hn hs hc P).1,
      (twistAddEquiv r n s hr hn hs hc).symm (splitPhi r n s hr hn hs hc P).2) =
      OriginalRCMilneSplitLocal318.sumDifference (Point r) P := by
  change (P.1+P.2,(twistAddEquiv r n s hr hn hs hc).symm
      (twistAddEquiv r n s hr hn hs hc (P.1-P.2))) = (P.1+P.2,P.1-P.2)
  rw [AddEquiv.symm_apply_apply]

def splitPsi (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0) (hs : s ≠ 0) (hc : n=s^2*r) :
    Point r × Point n →+ Point r × Point r where
  toFun p := (p.1+(twistAddEquiv r n s hr hn hs hc).symm p.2,
    p.1-(twistAddEquiv r n s hr hn hs hc).symm p.2)
  map_zero' := by apply Prod.ext <;> simp
  map_add' p q := by
    apply Prod.ext
    · change (p.1+q.1)+(twistAddEquiv r n s hr hn hs hc).symm (p.2+q.2) = _
      rw [map_add]
      change (p.1+q.1)+_ =
        (p.1+(twistAddEquiv r n s hr hn hs hc).symm p.2)+
          (q.1+(twistAddEquiv r n s hr hn hs hc).symm q.2)
      abel
    · change (p.1+q.1)-(twistAddEquiv r n s hr hn hs hc).symm (p.2+q.2) = _
      rw [map_add]
      change (p.1+q.1)-_ =
        (p.1-(twistAddEquiv r n s hr hn hs hc).symm p.2)+
          (q.1-(twistAddEquiv r n s hr hn hs hc).symm q.2)
      abel

theorem split_norm_coordinate (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : s ≠ 0) (hc : n=s^2*r) (P : Point r × Point r) :
    (splitPhi r n s hr hn hs hc P).1 = P.1+P.2 := rfl

theorem splitPsi_splitPhi (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : s ≠ 0) (hc : n=s^2*r) (P : Point r × Point r) :
    splitPsi r n s hr hn hs hc (splitPhi r n s hr hn hs hc P) =
      (P.1+P.1,P.2+P.2) := by
  let e := twistAddEquiv r n s hr hn hs hc
  change ((P.1+P.2)+e.symm (e (P.1-P.2)),(P.1+P.2)-e.symm (e (P.1-P.2))) = _
  rw [AddEquiv.symm_apply_apply]
  apply Prod.ext <;> abel

theorem splitPhi_splitPsi (r n s : F) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : s ≠ 0) (hc : n=s^2*r) (P : Point r × Point n) :
    splitPhi r n s hr hn hs hc (splitPsi r n s hr hn hs hc P) =
      (P.1+P.1,P.2+P.2) := by
  let e := twistAddEquiv r n s hr hn hs hc
  apply Prod.ext
  · change (P.1+e.symm P.2)+(P.1-e.symm P.2) = P.1+P.1
    abel
  · change e ((P.1+e.symm P.2)-(P.1-e.symm P.2)) = P.2+P.2
    have he : (P.1+e.symm P.2)-(P.1-e.symm P.2) = e.symm P.2+e.symm P.2 := by abel
    rw [he,map_add,AddEquiv.apply_symm_apply]

end OriginalRCMilneTwistPointGroup318

#print axioms OriginalRCMilneTwistPointGroup318.twistAddEquiv
#print axioms OriginalRCMilneTwistPointGroup318.splitPhi_normalized
#print axioms OriginalRCMilneTwistPointGroup318.splitPhi_splitPsi
