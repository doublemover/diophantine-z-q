module
public import OriginalRCMilneTwistedKummerPointAction318
import all OriginalRCMilneTwistedKummerPointAction318
import all OriginalRCMilneTwistPointGroup318
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section
noncomputable section

namespace OriginalRCMilneActualTwistedKummer318

open WeierstrassCurve.Affine ActualTwoDescentEllipticModel318
open OriginalRCMilneTwistPointGroup318 OriginalRCMilneTwistedKummerCore318
open OriginalRCMilneTwistedKummerPointAction318

variable {F : Type*} [Field F] [CharZero F]
local notation "Fb" => AlgebraicClosure F
local notation "Gal" => (Fb ≃ₐ[F] Fb)
local instance : DecidableEq Fb := Classical.decEq _
local notation "P" d => Point (algebraMap F Fb d)

theorem coefficient_relation (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) :
    algebraMap F Fb (k*d)=s^2*(algebraMap F Fb d) := by
  rw [hs,map_mul]

theorem parameter_ne {d : F} (hd : d ≠ 0) : algebraMap F Fb d ≠ 0 := by
  intro he
  exact hd ((algebraMap F Fb).injective (he.trans (map_zero _).symm))

/-- The very same ordered root scale, on the actual original curves
over the fixed algebraic closure, not an abstract conjugation. -/
def twist (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0)
    (hd : d ≠ 0) (hk : k ≠ 0) : P d ≃+ P (k*d) :=
  twistAddEquiv _ _ s (parameter_ne hd) (parameter_ne (mul_ne_zero hk hd)) hs0
    (coefficient_relation d k s hs)

theorem twist_some (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0)
    (hd : d ≠ 0) (hk : k ≠ 0) (x y : Fb)
    (H : (curve (algebraMap F Fb d)).toAffine.Nonsingular x y) :
    ∃ H' : (curve (algebraMap F Fb (k*d))).toAffine.Nonsingular (s^2*x) (s^3*y),
      twist d k s hs hs0 hd hk (.some x y H) = .some (s^2*x) (s^3*y) H' := by
  unfold twist
  rw [twistAddEquiv_apply]
  exact ⟨_,rfl⟩

/-- Galois acts on the second normalized coordinate by the *actual*
field-root sign; the ordering of the first split root is fixed. -/
theorem pointRho_twist (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0)
    (hd : d ≠ 0) (hk : k ≠ 0) (g : Gal) (Q : P d) :
    pointRho (k*d) g (twist d k s hs hs0 hd hk Q) =
      twist d k s hs hs0 hd hk (if rootFlip s g then -(pointRho d g Q) else pointRho d g Q) := by
  cases Q with
  | zero => cases h : rootFlip s g <;> simp [h,map_zero]
  | some x y H =>
    obtain ⟨Hg,hg⟩ := pointRho_some d g x y H
    obtain ⟨Ht,ht⟩ := twist_some d k s hs hs0 hd hk x y H
    obtain ⟨Hgt,hgt⟩ := pointRho_some (k*d) g (s^2*x) (s^3*y) Ht
    rw [ht,hgt,hg]
    have hr := root_sign k s hs g
    by_cases hf : rootFlip s g = true
    · rw [if_pos hf] at hr ⊢
      rw [WeierstrassCurve.Affine.Point.neg_some]
      obtain ⟨Hn,hn⟩ := twist_some d k s hs hs0 hd hk (g x)
        ((curve (algebraMap F Fb d)).toAffine.negY (g x) (g y))
        ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr Hg)
      rw [hn]
      simp only [WeierstrassCurve.Affine.Point.some.injEq,map_mul,map_pow,hr,curve_negY]
      constructor <;> ring
    · rw [if_neg hf] at hr ⊢
      obtain ⟨Hn,hn⟩ := twist_some d k s hs hs0 hd hk (g x) (g y) Hg
      rw [hn]
      simp only [WeierstrassCurve.Affine.Point.some.injEq,map_mul,map_pow,hr,and_self]

/-- The signed target Kummer condition is derived from being fixed
in the actual twist. It is not added as a character-matching axiom. -/
theorem actual_phi_representative (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (hd : d ≠ 0) (hk : k ≠ 0) (g : Gal)
    (X U T : P d) (hT : T+T=X+U)
    (hX : pointRho d g X=X)
    (hU : pointRho (k*d) g (twist d k s hs hs0 hd hk U)=twist d k s hs hs0 hd hk U) :
    let D := actualAction d k s hs hs0
    phiBoundary D X T g = (phiScalar D X T g,phiScalar D X T g) ∧
      phiScalar D X T g+phiScalar D X T g=0 := by
  let D := actualAction d k s hs hs0
  apply phi_diagonal D X U T g hT hX
  apply (twist d k s hs hs0 hd hk).injective
  exact (pointRho_twist d k s hs hs0 hd hk g U).symm.trans hU

theorem actual_psi_representative (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (g : Gal) (V W R : P d) (hR : R+R=V-W)
    (hfix : (actualAction d k s hs hs0).source g (V,W)=(V,W)) :
    let D := actualAction d k s hs hs0
    psiBoundary D V R g=(psiScalar D R g,psiScalar D R g) ∧
      psiScalar D R g+psiScalar D R g=0 :=
  psi_diagonal (actualAction d k s hs hs0) V W R g hR hfix

theorem actual_phi_independence (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X U T T' : P d) (h : T+T=X+U) (h' : T'+T'=X+U) :
    let D := actualAction d k s hs hs0
    ∃ E : P d × P d, OriginalRCMilneSplitLocal318.sumDifference (P d) E=0 ∧
      ∀ g, phiBoundary D X T' g-phiBoundary D X T g=D.source g E-E :=
  phi_independent (actualAction d k s hs hs0) X U T T' h h'

theorem actual_psi_independence (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (V W R R' : P d) (h : R+R=V-W) (h' : R'+R'=V-W) :
    let D := actualAction d k s hs hs0
    ∃ E : P d × P d, OriginalRCMilneSplitLocal318.sumDifference (P d) E=0 ∧
      ∀ g, psiBoundary D V R' g-psiBoundary D V R g=D.target g E-E :=
  psi_independent (actualAction d k s hs hs0) V W R R' h h'

/-- On the actual original curve, every point in this geometric
two-torsion subgroup is rational: the ordinate vanishes and its
abscissa is literally 0, d, or -3d. -/
theorem actual_two_fixed (d : F) (g : Gal) (Q : P d) (hQ : Q+Q=0) :
    pointRho d g Q=Q := by
  cases Q with
  | zero => exact map_zero _
  | some x y H =>
    have hy : y=-y := by
      have he : (.some x y H : P d) = -(.some x y H : P d) := by
        calc
          _ = ((.some x y H : P d)+(.some x y H : P d))-(.some x y H : P d) := by abel
          _ = _ := by rw [hQ,zero_sub]
      rw [WeierstrassCurve.Affine.Point.neg_some] at he
      have hz : x=x ∧ y=(curve (algebraMap F Fb d)).toAffine.negY x y := by
        simpa only [WeierstrassCurve.Affine.Point.some.injEq] using he
      exact hz.2.trans (curve_negY _ _ _)
    have hy0 : y=0 := by
      have he : (2:Fb)*y=0 := by linear_combination hy
      exact (mul_eq_zero.mp he).resolve_left two_ne_zero
    have hc := (curve_equation (algebraMap F Fb d) x y).mp H.1
    have hxprod : x*(x-algebraMap F Fb d)*(x+3*algebraMap F Fb d)=0 := by
      simpa only [hy0,zero_pow (by decide : (2:ℕ) ≠ 0)] using hc.symm
    have hx : g x=x := by
      rcases mul_eq_zero.mp hxprod with h | h
      · rcases mul_eq_zero.mp h with h₀ | h₁
        · rw [h₀,map_zero]
        · rw [sub_eq_zero.mp h₁,g.commutes]
      · have he : x=-(3*algebraMap F Fb d) := calc
          x = (x+3*algebraMap F Fb d)-3*algebraMap F Fb d := by abel
          _ = _ := by rw [h,zero_sub]
        rw [he,map_neg,map_mul,map_ofNat,g.commutes]
    obtain ⟨Hg,hg⟩ := pointRho_some d g x y H
    rw [hg]
    simp [WeierstrassCurve.Affine.Point.some.injEq,hx,hy0]

/-- Because this curve has actual rational E[2], lift independence
strengthens from modulo a coboundary to literal equality. -/
theorem actual_phi_equal_on_halves (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (X U T T' : P d) (h : T+T=X+U) (h' : T'+T'=X+U) (g : Gal) :
    let D := actualAction d k s hs hs0
    phiBoundary D X T' g=phiBoundary D X T g := by
  let D := actualAction d k s hs hs0
  obtain ⟨Z,hZ,hEq⟩ := actual_phi_independence d k s hs hs0 X U T T' h h'
  obtain ⟨hdiag,h₂⟩ := kernel_diagonal Z hZ
  have hfix : D.source g Z=Z := by
    calc
      _ = D.source g (Z.1,Z.1) := congrArg (D.source g) hdiag
      _ = (Z.1,Z.1) := by
        change (if rootFlip s g then ((pointRho d g Z.1),(pointRho d g Z.1))
          else ((pointRho d g Z.1),(pointRho d g Z.1)))=(Z.1,Z.1)
        rw [actual_two_fixed d g Z.1 h₂] <;> split <;> rfl
      _ = _ := hdiag.symm
  apply sub_eq_zero.mp
  rw [hEq g,hfix,sub_self]

end OriginalRCMilneActualTwistedKummer318

#print axioms OriginalRCMilneActualTwistedKummer318.actual_phi_representative
#print axioms OriginalRCMilneActualTwistedKummer318.actual_psi_representative
#print axioms OriginalRCMilneActualTwistedKummer318.actual_phi_independence
#print axioms OriginalRCMilneActualTwistedKummer318.actual_psi_independence
#print axioms OriginalRCMilneActualTwistedKummer318.actual_two_fixed
