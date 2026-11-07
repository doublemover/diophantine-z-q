module
public import GlobalGeneratorPoints318
public section
namespace GlobalSquareHalving318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- Exact remaining arithmetic assertion from the dual two-isogeny descent.
The dual curve is Y²=X³+4DX. This statement is not proved in this file. -/
@[expose] def DualSquareAbscissa : Prop :=
  ∀(X Y:K),Y^2=X^3+4*D*X → X≠0 → ∃k:K,k^2=X

theorem D_ne : D≠0 := by
  intro h
  have he := congrArg QuadraticAlgebra.re h
  norm_num [D,i,pair,pow_succ] at he

/-- An explicit half of (h²,hj), given the square root supplied by the dual
curve's arithmetic descent. No isogeny API or abstract group law is assumed. -/
theorem half_from_dual_root (h j k:K) (hj:j^2=h^4-D) (hk:k^2=2*(h^2+j)) :
    ∃Q:E.Point,Q+Q=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj) := by
  let x := (k^2+2*h*k)/2
  let y := k*x
  have hk0 : k≠0 := by
    intro hz
    have he : j= -h^2 := by rw [hz] at hk; linear_combination -(1/2:K)*hk
    have hd : D=0 := by rw [he] at hj; linear_combination hj
    exact D_ne hd
  have hxeq : x^2-k^2*x=D := by
    dsimp [x]
    linear_combination -hj + (h^2/2-j/2-k^2/4)*hk
  have hx0 : x≠0 := by intro hz; rw [hz] at hxeq; simp at hxeq; exact D_ne hxeq.symm
  have hy0 : y≠0 := mul_ne_zero hk0 hx0
  have he : E.Equation x y := by
    rw [equation_iff]
    simp only [E,zero_mul,mul_zero,add_zero]
    dsimp [y]
    linear_combination -x*hxeq
  have hn : E.Nonsingular x y :=
    (equation_iff_nonsingular_of_Δ_ne_zero RootPointAlgebra318.discriminant_nonzero).mp he
  have hden : y+y≠0 := by simpa [two_mul] using mul_ne_zero (show (2:K)≠0 by norm_num) hy0
  have hyn : y≠E.negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro hh
    exact hden (by linear_combination hh)
  have hm : E.slope x x y y=k+h := by
    rw [slope_of_Y_ne' (by simpa only [negY] using hyn)]
    simp only [E,zero_mul,add_zero,sub_zero,sub_neg_eq_add]
    apply (div_eq_iff hden).mpr
    dsimp [y]
    have hh : 2*x=k^2+2*h*k := by dsimp [x]; ring
    linear_combination hxeq + x*hh
  have hdx : E.addX x x (E.slope x x y y)=h^2 := by
    rw [addX,hm]
    simp only [E,zero_mul,add_zero,sub_zero]
    dsimp [x]; ring
  have hdy : E.addY x x y (E.slope x x y y)=h*j := by
    rw [addY,negAddY,negY,hdx,hm]
    simp only [E,zero_mul,sub_zero]
    dsimp [y,x]
    linear_combination (h/2)*hk
  refine ⟨Point.some x y hn,?_⟩
  rw [Point.add_self_of_Y_ne hyn]
  simp only [hdx,hdy]

/-- The exact dual-arithmetic assertion suffices for actual group halving
of every square-abscissa source chart, including both ordinate signs. -/
theorem square_halving (hd:DualSquareAbscissa) (h j:K) (hj:j^2=h^4-D) :
    ∃Q:E.Point,Q+Q=Point.some (h^2) (h*j) (RootPointAlgebra318.square_point h j hj) := by
  let X := 2*(h^2+j)
  let Y := 2*h*X
  have he : Y^2=X^3+4*D*X := by
    dsimp [X,Y]
    linear_combination -8*(h^2+j)*hj
  have hx : X≠0 := by
    intro hz
    have hj' : j= -h^2 := by dsimp [X] at hz; linear_combination (1/2:K)*hz
    have hd' : D=0 := by rw [hj'] at hj; linear_combination hj
    exact D_ne hd'
  obtain ⟨k,hk⟩ := hd X Y he hx
  exact half_from_dual_root h j k hj hk

end
end GlobalSquareHalving318
