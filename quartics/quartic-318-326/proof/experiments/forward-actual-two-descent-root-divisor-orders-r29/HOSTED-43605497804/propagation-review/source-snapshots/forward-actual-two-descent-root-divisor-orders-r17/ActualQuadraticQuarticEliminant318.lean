module
public import ActualGaussianSmallPrimeTail318
public section
noncomputable section
namespace ActualQuadraticQuarticEliminant318
set_option maxHeartbeats 7500000

/-- Integral pseudo-remainder of a genuine quartic modulo the actual
quadratic. No inversion of the quadratic leading coefficient is used. -/
@[expose] def linearTerm {R : Type*} [CommRing R] (a b c e f g h i : R) : R :=
  e*(-b^3+2*a*b*c)+f*a*(b^2-a*c)-g*a^2*b+h*a^3
@[expose] def constantTerm {R : Type*} [CommRing R] (a b c e f g h i : R) : R :=
  e*(-b^2*c+a*c^2)+f*a*b*c-g*a^2*c+i*a^3
@[expose] def eliminant {R : Type*} [CommRing R] (a b c e f g h i : R) : R :=
  let L := linearTerm a b c e f g h i
  let M := constantTerm a b c e f g h i
  a*M^2-b*L*M+c*L^2

lemma pseudo_identity {R : Type*} [CommRing R] (a b c e f g h i X : R) :
    a^3*(e*X^4+f*X^3+g*X^2+h*X+i)-
      (linearTerm a b c e f g h i*X+constantTerm a b c e f g h i)=
    (e*a^2*X^2+(f*a^2-e*a*b)*X+(e*b^2-e*a*c-f*a*b+g*a^2))*
      (a*X^2+b*X+c) := by
  dsimp [linearTerm,constantTerm]
  ring

lemma linear_identity {R : Type*} [CommRing R] (a b c L M X : R) :
    a*M^2-b*L*M+c*L^2=
      L^2*(a*X^2+b*X+c)-(a*L*X+b*L-a*M)*(L*X+M) := by ring

/-- Every genuine quadratic/quartic common integer divisor divides the
constructed SAME-fiber eliminant, including leading-coefficient primes.
Nonvanishing is a separate producer and is never assumed from this identity. -/
theorem common_divisor (a b c e f g h i X m : ℤ)
    (hF : m∣a*X^2+b*X+c) (hG : m∣e*X^4+f*X^3+g*X^2+h*X+i) :
    m∣eliminant a b c e f g h i := by
  have hdiff : m∣a^3*(e*X^4+f*X^3+g*X^2+h*X+i)-
      (linearTerm a b c e f g h i*X+constantTerm a b c e f g h i) := by
    rw [pseudo_identity]
    exact dvd_mul_of_dvd_right hF _
  have hlin : m∣linearTerm a b c e f g h i*X+constantTerm a b c e f g h i := by
    have hh := dvd_sub (dvd_mul_of_dvd_right hG (a^3)) hdiff
    simpa only [sub_sub_cancel] using hh
  dsimp [eliminant]
  rw [linear_identity]
  exact dvd_sub (dvd_mul_of_dvd_right hF _) (dvd_mul_of_dvd_right hlin _)

end ActualQuadraticQuarticEliminant318
