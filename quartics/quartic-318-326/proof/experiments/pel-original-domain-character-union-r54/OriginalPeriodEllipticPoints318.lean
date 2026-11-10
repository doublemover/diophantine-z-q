module
public import OriginalPeriodAffineBijection318
public import WeierstrassCubicNonsingular318
public import NormalizedWeierstrass318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
namespace OriginalPeriodEllipticPoints318
open OriginalPeriodWeierstrassCoordinates318 OriginalComplexPeriodPair318
open ComplexAffineFreeTranslation318
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Actual algebraic Weierstrass curve with the original period sums.
The y-coordinate is Pprime/2, so a4=-g2/4 and a6=-g3/4. -/
@[expose] def curve : WeierstrassCurve ℂ :=
  NormalizedWeierstrass318.model (12*(pair L).g₂) (216*(pair L).g₃)
lemma discriminant : (curve L).Δ=(pair L).g₂^3-27*(pair L).g₃^2 := by
  rw [curve,NormalizedWeierstrass318.model_discriminant]
  ring
instance curve_isElliptic : (curve L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [discriminant]; exact WeierstrassCubicNonsingular318.discriminant_ne_zero _)⟩

lemma equation_iff (a b : ℂ) : (curve L).toAffine.Equation a b ↔
    (2*b)^2=4*a^3-(pair L).g₂*a-(pair L).g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change b^2+0*a*b+0*b=a^3+0*a^2+(-(12*(pair L).g₂)/48)*a+(-(216*(pair L).g₃)/864) ↔ _
  constructor
  · intro h; linear_combination 4*h
  · intro h; linear_combination h/4

lemma nonsingular (q : {q : Torus L // q≠0}) :
    (curve L).toAffine.Nonsingular (x L q.val) (y L q.val/2) := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (show (curve L).Δ≠0 by rw [discriminant]; exact WeierstrassCubicNonsingular318.discriminant_ne_zero _)).mp
  rw [equation_iff]
  have h := cubic L q.val q.property
  convert h using 1 <;> ring

/-- The original zero maps to actual algebraic infinity; every other
point uses its original analytic pair, not an arbitrary set equivalence. -/
@[expose] def point (q : Torus L) : (curve L).toAffine.Point :=
  if hq : q=0 then .zero else .some (x L q) (y L q/2) (nonsingular L ⟨q,hq⟩)
lemma point_zero : point L 0=0 := by simp [point]
lemma point_nonzero (q : Torus L) (hq : q≠0) :
    point L q=.some (x L q) (y L q/2) (nonsingular L ⟨q,hq⟩) := dif_neg hq
lemma point_eq_zero (q : Torus L) : point L q=0 ↔ q=0 := by
  by_cases hq : q=0
  · simp [hq,point_zero]
  · rw [point_nonzero L q hq]
    simp only [WeierstrassCurve.Affine.Point.some_ne_zero,hq]

theorem point_injective : Function.Injective (point L) := by
  intro q r he
  by_cases hq : q=0
  · subst q
    exact ((point_eq_zero L r).mp (he.symm.trans (point_zero L))).symm
  have hr : r≠0 := by
    intro h
    subst r
    exact hq ((point_eq_zero L q).mp (he.trans (point_zero L)))
  rw [point_nonzero L q hq,point_nonzero L r hr] at he
  have hxy := WeierstrassCurve.Affine.Point.some.inj he
  have hy : y L q=y L r := by linear_combination 2*hxy.2
  have hab : affinePoint L ⟨q,hq⟩=affinePoint L ⟨r,hr⟩ := by
    apply Subtype.ext
    exact Prod.ext hxy.1 hy
  exact congrArg Subtype.val (OriginalPeriodAffineBijection318.affinePoint_injective L hab)

theorem point_surjective : Function.Surjective (point L) := by
  intro p
  cases p with
  | zero => exact ⟨0,point_zero L⟩
  | some a b hn =>
    have he := ((WeierstrassCurve.Affine.nonsingular_iff a b).mp hn).1
    have hc := (equation_iff L a b).mp he
    obtain ⟨q,hq⟩ := OriginalPeriodCubicSurjectivity318.affinePoint_surjective L ⟨(a,2*b),hc⟩
    have hx := congrArg (fun p => p.val.1) hq
    have hy := congrArg (fun p => p.val.2) hq
    refine ⟨q.val,?_⟩
    rw [point_nonzero L q.val q.property]
    apply WeierstrassCurve.Affine.Point.some.injEq.mpr
    refine ⟨hx,?_⟩
    change y L q.val=2*b at hy
    linear_combination hy/2

/-- Same original torus and native elliptic-curve point carrier, including
infinity, are genuinely bijective. Group law and scheme maps remain separate. -/
@[expose] def equivalence : Torus L ≃ (curve L).toAffine.Point :=
  Equiv.ofBijective (point L) ⟨point_injective L,point_surjective L⟩
end OriginalPeriodEllipticPoints318
