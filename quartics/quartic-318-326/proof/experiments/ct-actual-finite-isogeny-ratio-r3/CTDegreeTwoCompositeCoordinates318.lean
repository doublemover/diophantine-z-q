module
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section

namespace CTDegreeTwoCompositeCoordinates318

variable {K : Type*} [Field K] [CharZero K]

/-- On the literal long Weierstrass chart y²=x(x²+Ax+B), the
signed (ordinary ordinate) forward and reverse formulas compose to
the tangent formula. Both x and y are asserted; reflected ordinate
fails the second equation. -/
theorem signed_affine_composition (A B x y : K) (hx : x≠0) (hy : y≠0)
    (he : y^2=x*(x^2+A*x+B)) :
    let S := x+A+B/x
    let T := y-B*y/x^2
    let D := A^2-4*B
    let slope := (3*x^2+2*A*x+B)/(2*y)
    let X := slope^2-A-2*x
    (S-2*A+D/S)/4=X ∧ (T-D*T/S^2)/8=slope*(x-X)-y := by
  let U := x^2+A*x+B
  let E := x^2-B
  let P := 3*x^2+2*A*x+B
  let D := A^2-4*B
  have hxU : y^2=x*U := he
  have hu : U≠0 := by
    intro h0
    rw [h0,mul_zero] at hxU
    exact pow_ne_zero 2 hy hxU
  have hS : x+A+B/x=U/x := by dsimp [U]; field_simp [hx] <;> ring
  have hT : y-B*y/x^2=y*E/x^2 := by dsimp [E]; field_simp [hx] <;> ring
  have hX₁ : (U/x-2*A+D/(U/x))/4=E^2/(4*y^2) := by
    rw [hxU]
    dsimp [U,E,D] at *
    field_simp [hx,hu] <;> ring
  have hX₂ : (P/(2*y))^2-A-2*x=E^2/(4*y^2) := by
    have h4 : (4:K)≠0 := by norm_num
    have hSq : (P/(2*y))^2=P^2/(4*y^2) := by field_simp [hy] <;> ring
    rw [hSq]
    apply (eq_div_iff (mul_ne_zero h4 (pow_ne_zero 2 hy))).mpr
    have hC : P^2/(4*y^2)*(4*y^2)=P^2 := div_mul_cancel₀ _ (mul_ne_zero h4 (pow_ne_zero 2 hy))
    rw [sub_mul,sub_mul,hC,hxU]
    dsimp [P,U,E]
    ring
  have hY₁ : ((y*E/x^2)-D*(y*E/x^2)/(U/x)^2)/8 =
      E*(U^2-D*x^2)/(8*y^3) := by
    have hPoly : ((y*E/x^2)-D*(y*E/x^2)/(U/x)^2)/8 =
        y*E*(U^2-D*x^2)/(8*(x^2*U^2)) := by
      field_simp [hx,hu] <;> ring
    have hDen : x^2*U^2=y^4 := calc
      _=(x*U)^2 := (mul_pow x U 2).symm
      _=(y^2)^2 := by rw [hxU]
      _=_ := by ring
    rw [hPoly,hDen]
    field_simp [hy] <;> ring
  have hY₂ : (P/(2*y))*(x-E^2/(4*y^2))-y =
      E*(U^2-D*x^2)/(8*y^3) := calc
    _=(-8*(y^2)^2+4*y^2*P*x-P*E^2)/(8*y^3) := by
      field_simp [hy] <;> ring
    _=_ := by
      have hNum : -8*(y^2)^2+4*y^2*P*x-P*E^2=E*(U^2-D*x^2) := by
        rw [hxU]
        dsimp [U,P,E,D]
        ring
      rw [hNum]
  dsimp only
  change (x+A+B/x-2*A+D/(x+A+B/x))/4=(P/(2*y))^2-A-2*x ∧
    ((y-B*y/x^2)-D*(y-B*y/x^2)/(x+A+B/x)^2)/8=
      (P/(2*y))*(x-((P/(2*y))^2-A-2*x))-y
  rw [hS,hT,hX₂,hX₁,hY₁,hY₂]
  exact ⟨rfl,rfl⟩

/-- Any chosen nonzero-ordinate root on E' gives an actual lift
in E. The second root is kept for the exact nonzero proof. -/
theorem signed_forward_fiber (A B S T r : K) (hB : B≠0) (hS : S≠0)
    (hr : r^2=S) (he : T^2=S*(S^2-2*A*S+(A^2-4*B))) :
    let x := (S-A+T/r)/2
    let y := r*x
    x≠0 ∧ y^2=x*(x^2+A*x+B) ∧ x+A+B/x=S ∧ y-B*y/x^2=T := by
  let x := (S-A+T/r)/2
  let x' := (S-A-T/r)/2
  let y := r*x
  have hr0 : r≠0 := by
    intro h
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hr
    exact hS hr.symm
  have hSq : (T/r)^2=(S-A)^2-4*B := by
    rw [div_pow,hr]
    apply (div_eq_iff hS).mpr
    linear_combination he
  have hp : x*x'=B := by
    dsimp [x,x']
    have h2 : (2:K)≠0 := by norm_num
    field_simp [h2] <;> linear_combination -hSq
  have hx : x≠0 := by
    intro h
    rw [h,zero_mul] at hp
    exact hB hp.symm
  have hsum : x+x'=S-A := by dsimp [x,x']; ring
  have hdiff : x-x'=T/r := by dsimp [x,x']; ring
  have hU : x^2+A*x+B=S*x := by linear_combination -hp+x*hsum
  have hBdiv : B/x=x' := (div_eq_iff hx).2 ((mul_comm x' x).trans hp)
  have hT : B*(r*x)/x^2=r*x' := by
    apply (div_eq_iff (pow_ne_zero 2 hx)).2
    linear_combination -(r*x)*hp
  change x≠0 ∧ y^2=x*(x^2+A*x+B) ∧ x+A+B/x=S ∧ y-B*y/x^2=T
  refine ⟨hx,?_,?_,?_⟩
  · dsimp [y]
    rw [mul_pow,hr,hU]
    ring
  · rw [hBdiv]
    linear_combination hsum
  · dsimp [y]
    rw [hT]
    calc
      r*x-r*x'=r*(x-x') := by ring
      _=T := by rw [hdiff]; field_simp [hr0] <;> ring

end CTDegreeTwoCompositeCoordinates318

#print axioms CTDegreeTwoCompositeCoordinates318.signed_affine_composition
#print axioms CTDegreeTwoCompositeCoordinates318.signed_forward_fiber
