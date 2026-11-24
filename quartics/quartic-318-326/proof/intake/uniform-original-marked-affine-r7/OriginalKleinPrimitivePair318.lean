module
public import OriginalKleinMarkedCoordinates318
import Mathlib.Tactic
public section
noncomputable section
namespace OriginalKleinPrimitivePair318
open Polynomial OriginalKleinMarkedCoordinates318
variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
def P (t : K) := t*(t-32)*(t-76832)*(t+343)
theorem product (m : Row) (t : K) : P t =
    (t-b m)*(t-r0 m)*(t-r1 m)*(t-r2 m) := by
  cases m <;> dsimp only [P,b,r0,r1,r2] <;> push_cast <;> ring
private theorem fractions {d k w e0 e1 e2 e3 f y h z : K}
    (ht : e0*e1*e2*e3≠0) (hf : f≠0) (hy : y^2=f)
    (hw : d*w^2=k*(e1*f)*(e2*f)*(e3*f)) (hz : z=w/f^2*h) :
    d*e0*z^2/(e0*e1*e2*e3)=k*(h/y)^2 := by
  have hy' : y≠0 := fun H => hf (by simp_all)
  rw [hz, div_pow,mul_div_assoc']
  apply (div_eq_div_iff ht (pow_ne_zero 2 hy')).2
  rw [hy,mul_pow,div_pow]
  field_simp [hf]
  linear_combination (norm := ring_nf) e0*h^2*hw

/-- True differential-square read along an arbitrary tangent *of the actual
marked affine*, using only the quotient germ and the ordinate on that
named quartic. Works on either ordinary x chart. -/
theorem marked (m : Row) (j : Bool) (D : Derivation ℤ A K) (x t : A) (y : K)
    (relation : t*(F m j).eval₂ (Int.castRingHom A) x=(N m j).eval₂ (Int.castRingHom A) x)
    (curve : y^2=(F m j).eval₂ (Int.castRingHom K) (algebraMap A K x))
    (hy : y≠0) (hP : P (algebraMap A K t)≠0) :
    (kd m : K)*((algebraMap A K t)-(b m : K))*(D t)^2/P (algebraMap A K t)=
      (kn m : K)*(D x/y)^2 := by
  let ev := eval₂RingHom (Int.castRingHom K) (algebraMap A K x)
  change y^2=ev (F m j) at curve
  have ef : ev (F m j)≠0 := curve ▸ pow_ne_zero 2 hy
  have ⟨tv,dv⟩ := OriginalKleinMarkedJet318.read D x t (N m j) (F m j) relation ef
  let T := algebraMap A K t
  change T=ev (N m j)/ev (F m j) at tv
  have nv : ev (N m j)=T*ev (F m j) := ((eq_div_iff ef).mp tv).symm
  have w := congrArg ev (identity m j)
  have ec (a : ℤ) : ev (C a)=(a:K) := eval₂_C ..
  simp only [map_mul,map_sub,map_pow,ec] at w
  change (kd m:K)*(ev (derivative (N m j))*ev (F m j)-ev (N m j)*ev (derivative (F m j)))^2=
     (kn m:K)*(ev (N m j)-r0 m*ev (F m j))*(ev (N m j)-r1 m*ev (F m j))*
     (ev (N m j)-r2 m*ev (F m j)) at w
  rw [nv] at w
  simp only [←sub_mul] at w
  rw [product m] at hP ⊢
  apply fractions hP ef curve w
  change D t=_ at dv
  rw [←nv]
  exact dv
/-- On one actual affine carrying both marked quotient germs, the two literal
sections (not merely a spanning pair) are S0 = 205800 Q and S1 = (25725/4)tQ.
The sign of the two primitive Jacobian forms is never chosen. -/
theorem original_pair [CharZero K] (D : Derivation ℤ A K) (t x0 x1 : A)
    (j0 j1 : Bool) (y0 y1 : K)
    (h0 : t*(F .m105 j0).eval₂ (Int.castRingHom A) x0=(N .m105 j0).eval₂ (Int.castRingHom A) x0)
    (h1 : t*(F .m70 j1).eval₂ (Int.castRingHom A) x1=(N .m70 j1).eval₂ (Int.castRingHom A) x1)
    (c0 : y0^2=(F .m105 j0).eval₂ (Int.castRingHom K) (algebraMap A K x0))
    (c1 : y1^2=(F .m70 j1).eval₂ (Int.castRingHom K) (algebraMap A K x1))
    (n0 : y0≠0) (n1 : y1≠0) (hP : P (algebraMap A K t)≠0) :
    let T := algebraMap A K t
    let Q := (D t)^2/P T
    let w0 := D x0/y0
    let w1 := 2*(D x1/y1)
    205800*Q=343*w0^2-75*w1^2 ∧ (25725/4)*T*Q=343*w0^2 := by
  dsimp only
  have a := marked .m105 j0 D x0 t y0 h0 c0 n0 hP
  have v := marked .m70 j1 D x1 t y1 h1 c1 n1 hP
  norm_num only [kd,kn,b,Int.cast_ofNat,Int.cast_zero,sub_zero] at a v
  simp only [div_eq_mul_inv] at a v ⊢
  constructor
  · linear_combination (343/4)*a - (75/4)*v
  · linear_combination (343/4)*a
end OriginalKleinPrimitivePair318
#print axioms OriginalKleinPrimitivePair318.marked
#print axioms OriginalKleinPrimitivePair318.original_pair
