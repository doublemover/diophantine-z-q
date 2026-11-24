module
public import OriginalScalarProjectiveObstruction318
public section
namespace OriginalScalarExceptionalMap318
open OriginalMarkedIntPolynomialCertificate318 OriginalScalarProjectiveObstruction318
open OriginalRadixHZCertificate318 OriginalPhysicalHZ210Identity318
@[expose] def nn : List ℤ := [10976,0,21952,0,10976]
@[expose] def dd : List ℤ := [43,-600,986,600,43]
@[expose] def vv : List ℤ := [5122848,-71481600,117468096,71481600,5122848]
@[expose] def hform (a b : E) : List ℤ → E
  | [] => .p []
  | c :: l => .add (.scale c (pw b l.length)) (.mul a (hform a b l))
theorem ev_form {F : Type*} [CommRing F] (z : F) (a b : E) (l : List ℤ) :
    Ev z (hform a b l) = homog (Ev z a) (Ev z b) l := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [hform,Ev,ev_pw,ih,homog]
@[expose] def condition (f g q : List ℤ) : E :=
  .add (hform (.p nn) (.p vv) g) (.scale (-1) (.mul (.p f) (.p q)))
theorem vv_eq {F : Type*} [CommRing F] (z : F) : horner z vv=119136*horner z dd := by
  simp [horner,vv,dd]; ring
/-- If f divides the cleared scalar image and that image has a rootless reduction,
f cannot vanish at any ordinary point over the original rational square line. -/
theorem excludes {K : Type*} [Field K] [CharZero K] (z : K) (x : ℚ)
    (d : horner z dd≠0) (hz : horner z nn=(x:K)^2*horner z vv)
    (f g q : List ℤ) (he : Ev z (condition f g q)=0)
    (hg : horner (x^2) g≠0) : horner z f≠0 := by
  intro h
  simp only [condition,Ev,ev_form,h,mul_zero,zero_mul,add_zero,hz] at he
  have hh := homog_subst ((x:K)^2) (horner z vv) g
  rw [he,mul_zero] at hh
  have hv : horner z vv≠0 := by rw [vv_eq]; exact mul_ne_zero (by norm_num) d
  have hk : horner ((x:K)^2) g=0 := (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hv)
  apply hg
  apply (Rat.castHom K).injective
  rw [OriginalPhysicalHZ210Identity318.horner_eq,
      OriginalPhysicalHZ210Map318.horner_map,map_pow,map_zero]
  rw [← OriginalPhysicalHZ210Identity318.horner_eq]; exact hk
end OriginalScalarExceptionalMap318
#print axioms OriginalScalarExceptionalMap318.excludes
