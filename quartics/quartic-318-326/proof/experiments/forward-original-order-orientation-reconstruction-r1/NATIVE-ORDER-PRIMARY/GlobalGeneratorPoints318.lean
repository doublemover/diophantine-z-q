module
public import RawGroupAnchor318
public import FiniteSquareTest318
public section
namespace GlobalGeneratorPoints318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def xR : K := pair 1 1
@[expose] def yR : K := pair 0 2
@[expose] def slopeR : K := pair 3 (-1/4)

theorem equationR : E.Equation xR yR := by
  rw [equation_iff]
  ext <;> norm_num [E,xR,yR,D,i,pair,pow_succ]
theorem yR_ne : yR≠0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.im h
  norm_num [yR,pair] at hh

theorem nonsingularR : E.Nonsingular xR yR :=
  (equation_iff_nonsingular_of_Δ_ne_zero RootPointAlgebra318.discriminant_nonzero).mp equationR
@[expose] def R : E.Point := .some xR yR nonsingularR

theorem slopeR_actual : E.slope xR xR yR yR=slopeR := by
  rw [slope_of_Y_ne']
  · simp only [E,zero_mul,add_zero,sub_zero,sub_neg_eq_add]
    apply (div_eq_iff (show yR+yR≠0 by simpa [two_mul] using mul_ne_zero (show (2:K)≠0 by norm_num) yR_ne)).mpr
    ext <;> norm_num [slopeR,xR,yR,D,i,pair,pow_succ]
  · simp only [E,zero_mul,sub_zero]
    intro h
    have hh : 2*yR=0 := by linear_combination h
    exact (mul_ne_zero (by norm_num) yR_ne) hh

/-- The global generator candidate doubles to the exact point used by every
source-local label theorem. This is an equality in Mathlib's actual group. -/
theorem double_R : R+R=P := by
  have hy : yR≠E.negY xR yR := by
    simp only [negY,E,zero_mul,sub_zero]
    intro h
    have hh : 2*yR=0 := by linear_combination h
    exact (mul_ne_zero (by norm_num) yR_ne) hh
  have hx : E.addX xR xR (E.slope xR xR yR yR)=xP := by
    rw [slopeR_actual,addX]
    ext <;> norm_num [E,xR,xP,slopeR,pair,pow_succ]
  have hy' : E.addY xR xR yR (E.slope xR xR yR yR)=yP := by
    rw [addY,negAddY,negY,hx,slopeR_actual]
    ext <;> norm_num [E,xR,xP,yR,yP,slopeR,pair,pow_succ]
  rw [R,Point.add_self_of_Y_ne hy]
  simp only [hx,hy',P]

theorem two_zsmul_R : (2:ℤ) • R=P := by simpa [two_zsmul] using double_R

@[expose] def torsionX (i:Fin 3) : K := if i=0 then 0 else if i=1 then pair 3 (-1) else pair (-3) 1

theorem torsion_equation (i:Fin 3) : E.Equation (torsionX i) 0 := by
  fin_cases i <;> rw [equation_iff] <;> ext <;> norm_num [E,torsionX,D,i,pair,pow_succ]

theorem torsion_nonsingular (i:Fin 3) : E.Nonsingular (torsionX i) 0 :=
  (equation_iff_nonsingular_of_Δ_ne_zero RootPointAlgebra318.discriminant_nonzero).mp (torsion_equation i)
@[expose] def T (i:Fin 3) : E.Point := Point.some (torsionX i) 0 (torsion_nonsingular i)

theorem double_T (i:Fin 3) : T i+T i=0 := by
  apply Point.add_self_of_Y_eq
  simp [negY,E]

theorem R_ne_torsionX (i:Fin 3) : xR≠torsionX i := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  fin_cases i <;> norm_num [xR,torsionX,pair] at hr

@[expose] def translateX (i:Fin 3) : K :=
  if i=0 then pair 23 (-17) else if i=1 then pair 2 4 else pair (5/2) (-2)

/-- All four non-torsion survivors in the bounded search are translates of
R by the displayed actual 2-torsion points. -/
theorem translate_coordinates (i:Fin 3) :
    ∃(y:K)(h:E.Nonsingular (translateX i) y),R+T i=Point.some _ y h := by
  let m := E.slope xR (torsionX i) yR 0
  let xx := E.addX xR (torsionX i) m
  let yy := E.addY xR (torsionX i) yR m
  have hr : E.Nonsingular xx yy := nonsingular_add nonsingularR (torsion_nonsingular i)
    (fun hh => R_ne_torsionX i hh.1)
  have hadd : R+T i=Point.some xx yy hr := Point.add_of_X_ne (R_ne_torsionX i)
  have hx : xx=translateX i := by
    change E.addX xR (torsionX i) (E.slope xR (torsionX i) yR 0)=_
    rw [addX,slope_of_X_ne (R_ne_torsionX i)]
    fin_cases i <;> ext <;> norm_num [E,xR,yR,torsionX,translateX,pair,pow_succ,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def]
  simp only [hx] at hr hadd
  exact ⟨yy,hr,hadd⟩

/-- The exact group-theoretic classification delivered by the finite
abscissa certificate. Negation is retained explicitly. -/
@[expose] def Classified (Q:E.Point) : Prop :=
  (Q+Q=0) ∨ ∃U:E.Point,U+U=0 ∧ (Q=R+U ∨ Q= -(R+U))

theorem classified_torsion_x (i:Fin 3) (y:K) (h:E.Nonsingular (torsionX i) y) :
    Classified (Point.some _ y h) := by
  have he := (Point.X_eq_iff (h₁:=h) (h₂:=torsion_nonsingular i)).mp rfl
  change Point.some _ y h=T i ∨ Point.some _ y h= -T i at he
  left
  rcases he with he|he
  · rw [he]; exact double_T i
  · rw [he,←neg_add, double_T]; simp

theorem classified_R_x (y:K) (h:E.Nonsingular xR y) :
    Classified (Point.some _ y h) := by
  have he := (Point.X_eq_iff (h₁:=h) (h₂:=nonsingularR)).mp rfl
  right
  refine ⟨0,by simp,?_⟩
  simpa [R] using he

theorem classified_translate_x (i:Fin 3) (y:K) (h:E.Nonsingular (translateX i) y) :
    Classified (Point.some _ y h) := by
  obtain ⟨yy,hh,he⟩ := translate_coordinates i
  have hp := (Point.X_eq_iff (h₁:=h) (h₂:=hh)).mp rfl
  right
  refine ⟨T i,double_T i,?_⟩
  simpa only [←he] using hp

/-- A curve point at any of the seven explicit abscissae is either actual
2-torsion or a signed translate of R by actual 2-torsion. -/
theorem classified_survivor (u v:ℚ) (y:K) (h:E.Nonsingular (pair u v) y)
    (hs:FiniteSquareTest318.Survivor u v) : Classified (Point.some _ y h) := by
  rcases hs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · convert classified_torsion_x 0 y (by simpa [torsionX,pair] using h) using 1 <;> simp [torsionX,pair]
  · exact classified_torsion_x 1 y h
  · exact classified_torsion_x 2 y h
  · exact classified_R_x y h
  · exact classified_translate_x 0 y h
  · exact classified_translate_x 1 y h
  · exact classified_translate_x 2 y h

end
end GlobalGeneratorPoints318
