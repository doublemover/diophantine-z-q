module
public import DualSignature318
public import Mathlib.NumberTheory.Pell
public section
namespace PositiveUnitSquare318
open ConcreteG8Domain
set_option maxHeartbeats 0

@[expose] def fundamental : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

theorem fundamental_isFundamental : Pell.IsFundamental fundamental := by
  refine ⟨by norm_num [fundamental],by norm_num [fundamental],?_⟩
  intro b hb
  change 3≤b.x
  by_contra! hh
  have hx:b.x=2 := by omega
  have he:=b.prop
  rw [hx] at he
  norm_num at he
  omega

@[expose] def pellMap : Pell.Solution₁ 2 →* K where
  toFun a:=pair a.x a.y
  map_one':=by ext <;> simp [pair]
  map_mul' a b:=by
    rw [pair_product]
    ext <;> simp [pair,Pell.Solution₁.x_mul,Pell.Solution₁.y_mul] <;> ring

theorem pellMap_fundamental : pellMap fundamental=(1+i)^2 := by
  change pair 3 2=(1+i)^2
  ext <;> norm_num [i,pair,pow_two,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

/-- Every norm-one integer pair with positive rational part is an actual
square in Q(sqrt2). This is the totally-positive unit step, independent of
any PID or prime-ideal factorization assumption. -/
theorem pell_positive_square (a:Pell.Solution₁ 2) (ha:0<a.x) :
    ∃k:K,k^2=pellMap a := by
  obtain ⟨n,hn|hn⟩:=fundamental_isFundamental.eq_zpow_or_neg_zpow a
  · refine ⟨(1+i)^n,?_⟩
    rw [hn,pellMap.map_zpow,pellMap_fundamental]
    simp only [←zpow_natCast,←zpow_mul]
    congr 1
    ring
  · have hx:=Pell.Solution₁.x_zpow_pos (a:=fundamental) (by norm_num [fundamental]) n
    rw [hn,Pell.Solution₁.x_neg] at ha
    omega

/-- In the concrete order Z[sqrt2], total positivity forces an actual unit
to have norm1 and hence to be a square in the quadratic field. -/
theorem totally_positive_unit_square (u:Zsqrtd (2:ℤ)) (hu:IsUnit u)
    (hp:∀(s:ℝ)(hs:s^2=2),0<FiniteScale318.realPlace s hs (pair u.re u.im)) :
    ∃k:K,k^2=pair u.re u.im := by
  let r:ℝ:=Real.sqrt 2
  have hr:r^2=2 := Real.sq_sqrt (by norm_num)
  have hnr:(-r)^2=2 := by simpa only [neg_sq] using hr
  have hpos:=hp r hr
  have hneg:=hp (-r) hnr
  rw [FiniteScale318.realPlace_pair] at hpos hneg
  push_cast at hpos hneg
  have ha:0<u.re := by exact_mod_cast (show (0:ℝ)<(u.re:ℝ) by linarith)
  have hnpos:0<u.norm := by
    have hm:=mul_pos hpos hneg
    have he:((u.re:ℝ)+(u.im:ℝ)*r)*((u.re:ℝ)+(u.im:ℝ)*(-r))=
        (u.re:ℝ)^2-2*(u.im:ℝ)^2 := by nlinarith [hr]
    rw [he] at hm
    exact_mod_cast (show (0:ℝ)<(u.re:ℝ)*(u.re:ℝ)-2*(u.im:ℝ)*(u.im:ℝ) by nlinarith)
  have habs:=Int.isUnit_iff_abs_eq.mp ((Zsqrtd.isUnit_iff_norm_isUnit u).mp hu)
  have hn:u.re^2-2*u.im^2=1 := by
    rw [abs_of_pos hnpos] at habs
    simpa only [Zsqrtd.norm_def,pow_two,mul_assoc] using habs
  exact pell_positive_square (Pell.Solution₁.mk u.re u.im hn) ha

end PositiveUnitSquare318
#print axioms PositiveUnitSquare318.fundamental_isFundamental
#print axioms PositiveUnitSquare318.pell_positive_square
