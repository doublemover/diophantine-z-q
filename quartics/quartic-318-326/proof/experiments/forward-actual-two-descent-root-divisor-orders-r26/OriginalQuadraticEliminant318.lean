module
public import OriginalGoodLatticeSieveUnion318
public section
noncomputable section
namespace OriginalQuadraticEliminant318
set_option maxHeartbeats 4000000

/-- Literal degree-two Sylvester eliminant, with its coefficients kept
integral. It is allowed to vanish when both padded degrees drop; consumers
must prove nonvanishing separately, not infer it from this identity. -/
@[expose] def eliminant {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)

lemma bezout_identity {R : Type*} [CommRing R] (a b c d e f h : R) :
    eliminant a b c d e f=
      (d*(a*e-b*d)*h-a*d*f+a*e^2-b*d*e+c*d^2)*(a*h^2+b*h+c)+
      (-a*(a*e-b*d)*h+a^2*f-a*b*e-a*c*d+b^2*d)*(d*h^2+e*h+f) := by
  dsimp [eliminant]
  ring

/-- Actual integer common divisors divide the explicitly constructed
eliminant at the SAME remaining coordinates, without division by a leading
coefficient and without excluding its prime divisors. -/
theorem common_divisor (a b c d e f h m : ℤ)
    (hF : m∣a*h^2+b*h+c) (hG : m∣d*h^2+e*h+f) :
    m∣eliminant a b c d e f := by
  rw [bezout_identity a b c d e f h]
  exact dvd_add (dvd_mul_of_dvd_right hF _) (dvd_mul_of_dvd_right hG _)

/-- Quantitative coefficient-size bound for this exact eliminant; useful
for the number of large prime divisors of a nonzero fiber value. -/
theorem eliminant_abs_bound (a b c d e f : ℤ) (H K : ℝ)
    (hH : 0≤H) (hK : 0≤K)
    (ha : |(a:ℝ)|≤H) (hb : |(b:ℝ)|≤H) (hc : |(c:ℝ)|≤H)
    (hd : |(d:ℝ)|≤K) (he : |(e:ℝ)|≤K) (hf : |(f:ℝ)|≤K) :
    |(eliminant a b c d e f:ℝ)|≤8*H^2*K^2 := by
  have bound (x y z w : ℝ) (hx : |x|≤H) (hy : |y|≤K)
      (hz : |z|≤H) (hw : |w|≤K) : |x*y-z*w|≤2*H*K := by
    calc
      _ ≤ |x*y|+|z*w| := abs_sub _ _
      _ = |x|*|y|+|z|*|w| := by rw [abs_mul,abs_mul]
      _ ≤ H*K+H*K := add_le_add (mul_le_mul hx hy (abs_nonneg _) hH)
        (mul_le_mul hz hw (abs_nonneg _) hH)
      _ = _ := by ring
  have h1 := bound (a:ℝ) f c d ha hf hc hd
  have h2 := bound (a:ℝ) e b d ha he hb hd
  have h3 := bound (b:ℝ) f c e hb hf hc he
  have hm := mul_le_mul h2 h3 (abs_nonneg _) (by positivity : 0≤2*H*K)
  have hs := mul_self_le_mul_self (abs_nonneg _) h1
  push_cast [eliminant]
  have hh := abs_sub (((a:ℝ)*f-c*d)^2) (((a:ℝ)*e-b*d)*((b:ℝ)*f-c*e))
  rw [abs_pow,abs_mul] at hh
  nlinarith only [hh,hm,hs]

end OriginalQuadraticEliminant318
