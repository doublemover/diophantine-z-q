module
public import OriginalRCMilneTwistPointGroup318
public import OriginalRCMilneTwistedKummerCore318
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.LinearCombination

public section
noncomputable section

namespace OriginalRCMilneTwistedKummerPointAction318

open WeierstrassCurve WeierstrassCurve.Affine ActualTwoDescentEllipticModel318
open OriginalRCMilneTwistedKummerCore318

variable {F : Type*} [Field F] [CharZero F]
local notation "Fb" => AlgebraicClosure F
local notation "Gal" => (Fb ≃ₐ[F] Fb)
local instance : DecidableEq Fb := Classical.decEq _

abbrev rawCurve (d : F) : WeierstrassCurve.Affine Fb :=
  (curve d).toAffine.baseChange Fb

theorem curve_base (d : F) :
    (curve d).toAffine.baseChange Fb = (curve (algebraMap F Fb d)).toAffine := by
  ext <;> simp [WeierstrassCurve.baseChange,WeierstrassCurve.map,
    WeierstrassCurve.toAffine,curve,map_ofNat]

def pointCongr {K : Type*} [Field K] [DecidableEq K]
    {V W : WeierstrassCurve.Affine K} (h : V=W) : V.Point ≃+ W.Point := by
  subst W
  exact AddEquiv.refl _

@[simp] theorem pointCongr_zero {K : Type*} [Field K] [DecidableEq K]
    {V W : WeierstrassCurve.Affine K} (h : V=W) :
    pointCongr h (0 : V.Point) = 0 := map_zero _

theorem pointCongr_some {K : Type*} [Field K] [DecidableEq K]
    {V W : WeierstrassCurve.Affine K} (h : V=W) (x y : K) (H : V.Nonsingular x y) :
    pointCongr h (.some x y H) = .some x y (h ▸ H) := by
  subst W
  rfl

theorem pointCongr_symm {K : Type*} [Field K] [DecidableEq K]
    {V W : WeierstrassCurve.Affine K} (h : V=W) :
    (pointCongr h).symm = pointCongr h.symm := by
  subst W
  rfl

/-- Point action from the pinned Mathlib base-change homomorphism on
the actual original curve; no CT/thin names or alternate curve model. -/
def rawRho (d : F) : Gal →* AddMonoid.End (rawCurve d).Point where
  toFun g := WeierstrassCurve.Affine.Point.map (W' := (curve d).toAffine) g.toAlgHom
  map_one' := by
    apply AddMonoidHom.ext
    intro P
    cases P <;> rfl
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro P
    have hm : (g*h).toAlgHom = g.toAlgHom.comp h.toAlgHom := by
      apply AlgHom.ext
      intro x
      rfl
    change WeierstrassCurve.Affine.Point.map (g*h).toAlgHom P =
      WeierstrassCurve.Affine.Point.map g.toAlgHom
        (WeierstrassCurve.Affine.Point.map h.toAlgHom P)
    rw [hm,WeierstrassCurve.Affine.Point.map_map]

def pointRho (d : F) : Gal →* AddMonoid.End (Point (algebraMap F Fb d)) where
  toFun g :=
    let e := pointCongr (curve_base d)
    e.toAddMonoidHom.comp ((rawRho d g).comp e.symm.toAddMonoidHom)
  map_one' := by
    apply AddMonoidHom.ext
    intro P
    let e := pointCongr (curve_base d)
    change e (rawRho d 1 (e.symm P)) = P
    rw [map_one] <;> exact e.apply_symm_apply P
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro P
    let e := pointCongr (curve_base d)
    change e (rawRho d (g*h) (e.symm P)) =
      e (rawRho d g (e.symm (e (rawRho d h (e.symm P)))))
    rw [map_mul,e.symm_apply_apply] <;> rfl

theorem pointRho_some (d : F) (g : Gal) (x y : Fb)
    (H : (curve (algebraMap F Fb d)).toAffine.Nonsingular x y) :
    ∃ H' : (curve (algebraMap F Fb d)).toAffine.Nonsingular (g x) (g y),
      pointRho d g (.some x y H) = .some (g x) (g y) H' := by
  let e := curve_base d
  have he := pointCongr_symm e
  change ∃ H', pointCongr e
    (WeierstrassCurve.Affine.Point.map g.toAlgHom ((pointCongr e).symm (.some x y H))) =
      .some (g x) (g y) H'
  rw [he,pointCongr_some,WeierstrassCurve.Affine.Point.map_some,pointCongr_some]
  exact ⟨_,rfl⟩

/-- The bit is obtained from the actual chosen root, not an independent
quadratic character or two unrelated absolute actions. -/
def rootFlip (s : Fb) (g : Gal) : Bool := if g s = s then false else true

theorem root_sign (k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (g : Gal) :
    g s = if rootFlip s g then -s else s := by
  have he : (g s)^2=s^2 := by
    rw [← map_pow,hs,g.commutes]
  by_cases h : g s=s
  · simp [rootFlip,h]
  · have h' : g s=-s := (sq_eq_sq_iff_eq_or_eq_neg.mp he).resolve_left h
    simp [rootFlip,h,h']

theorem rootFlip_mul (k : F) (s : Fb) (hs : s^2=algebraMap F Fb k)
    (hs0 : s ≠ 0) (g h : Gal) :
    rootFlip s (g*h) = Bool.xor (rootFlip s g) (rootFlip s h) := by
  have hsgn : s ≠ -s := by
    intro hn
    have h₂ : (2:Fb)*s=0 := by linear_combination hn
    exact hs0 ((mul_eq_zero.mp h₂).resolve_left two_ne_zero)
  have hInj : Function.Injective (fun b : Bool => if b then -s else s) := by
    intro a b he
    cases a <;> cases b
    · rfl
    · exact (hsgn (by simpa using he)).elim
    · exact (hsgn (by simpa using he.symm)).elim
    · rfl
  apply hInj
  rw [← root_sign k s hs (g*h),AlgEquiv.mul_apply,root_sign k s hs h]
  cases hg : rootFlip s g <;> cases hh : rootFlip s h <;>
    simp [root_sign k s hs g,hg,hh,Bool.xor]

/-- Actual ordered geometric action induced by the specified root and
Mathlib action on the literal original elliptic curve. -/
def actualAction (d k : F) (s : Fb) (hs : s^2=algebraMap F Fb k) (hs0 : s ≠ 0) :
    OrderedAction Gal (Point (algebraMap F Fb d)) where
  ρ := pointRho d
  flip := rootFlip s
  flip_mul := rootFlip_mul k s hs hs0
  flip_one := by simp [rootFlip,AlgEquiv.one_apply]

end OriginalRCMilneTwistedKummerPointAction318

#print axioms OriginalRCMilneTwistedKummerPointAction318.actualAction
