module
public import ActualGaussianWeberMixedStockCoordinates318
import all ActualGaussianWeberMixedPolynomial318
public section
noncomputable section

namespace ActualGaussianWeberFiniteAnchorTranslate318
open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberMixedPolynomial318 ActualGaussianWeberMixedValuedData318
open ActualGaussianWeberMixedStockCoordinates318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)

private theorem anchor_eq : (V.subtype (0:V))^2=(V.subtype (0:V))^3-V.subtype (0:V) := by
  simp

/-- Literal finite stock point (0,0), not a hypothetical chosen section. -/
def anchor (hF : (2:F) ≠ 0) : WP F :=
  Point.some (V.subtype (0:V)) (V.subtype (0:V)) (nonsing_of_equation hF (anchor_eq V))

private theorem pointTransport {x y x' y' : F}
    {h : (curve F).toAffine.Nonsingular x y}
    {h' : (curve F).toAffine.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') : Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

structure Read (hF : (2:F) ≠ 0) {P : WP F} (D : OriginData V P) where
  x : V
  u : V
  x_residue : residue V x=0
  u_residue : residue V u=1
  ns : (curve F).toAffine.Nonsingular (V.subtype x) (V.subtype (-D.t*u))
  point_exact : P+anchor V hF=Point.some (V.subtype x) (V.subtype (-D.t*u)) ns

/-- The actual finite translate of a kernel point reads its chart
parameter with the exact sign and a residue-one multiplier. -/
theorem read (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    {P : WP F} (hP : specialize V h2 P=Point.zero) (D : OriginData V P) :
    Nonempty (Read V hF D) := by
  let h₀ := nonsing_of_equation hF (anchor_eq V)
  have hT : anchor V hF = Point.some (V.subtype (0:V)) (V.subtype (0:V)) h₀ := rfl
  by_cases hO : P=Point.zero
  · subst P
    have htz : V.subtype D.t=0 := D.t_exact
    have ht : D.t=0 := V.subtype_injective (htz.trans (map_zero V.subtype).symm)
    have hy : V.subtype (-D.t*(1:V))=V.subtype (0:V) := by rw [ht,neg_zero,zero_mul]
    have hn : (curve F).toAffine.Nonsingular (V.subtype (0:V)) (V.subtype (-D.t*(1:V))) := by
      rw [hy]
      exact h₀
    refine ⟨⟨0,1,map_zero _,map_one _,hn,?_⟩⟩
    change (0:WP F)+anchor V hF=_
    rw [zero_add,hT]
    exact pointTransport rfl hy.symm
  · obtain ⟨K,hXY,hAdd⟩ := mixed_stock_coordinates V h2 P 0 0 h₀ hP hO D
    have hb : K.beta=1 := by simpa using K.beta_inv
    have hY : K.Y= -D.t*K.u := by
      simp [K.y_formula,H,hb] <;> ring
    have hY' : V.subtype K.Y=V.subtype (-D.t*K.u) := congrArg V.subtype hY
    have hn : (curve F).toAffine.Nonsingular (V.subtype K.X) (V.subtype (-D.t*K.u)) := by
      rw [←hY']
      exact hXY
    refine ⟨⟨K.X,K.u,K.x_residue.trans (map_zero _),K.u_res,hn,?_⟩⟩
    rw [hT,hAdd]
    exact pointTransport rfl hY'

/-- The same kernel point translates a finite abscissa reducing to 0.
At a fixed original scale s, the coefficient of the new ordinate
is d−c, when the old ordinate is s*d and the chart is s*c. -/
theorem mixed_scaled_ordinate {s t w A B c d : V}
    (K : IntegralData V t w A B) (hs : s∈maximalIdeal V)
    (ht : t=s*c) (hB : B=s*d) (hA : residue V A=0) :
    ∃ e : V, K.Y=s*e ∧ residue V e=residue V d-residue V c := by
  let C : V := 2*d+(3*A^2-1)*c-(A^3+A)*(s^2*c^3*K.u)
  let e : V := -d+(1+B*w)*K.u*K.beta^3*C
  have hw : w=s^3*c^3*K.u := K.w_relation.trans
    ((congrArg (fun z : V => z^3*K.u) ht).trans (by rw [mul_pow]))
  have hC : H t w A B=s*C := by
    unfold H C
    linear_combination 2*hB+(3*A^2-1)*ht-(A^3+A)*hw
  refine ⟨e,?_,?_⟩
  · have hNeg : -B= -(s*d) := congrArg (fun x : V => -x) hB
    rw [K.y_formula,hC,hNeg]
    dsimp only [e]
    ring
  · have hs0 := (residue_eq_zero_iff s).mpr hs
    have hB0 : residue V B=0 := by rw [hB,map_mul,hs0,zero_mul]
    simp [e,C,hA,hs0,hB0,K.u_res,K.beta_res,map_ofNat] <;> ring

end ActualGaussianWeberFiniteAnchorTranslate318
