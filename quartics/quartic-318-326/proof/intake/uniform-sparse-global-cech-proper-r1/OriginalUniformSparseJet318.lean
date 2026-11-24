module
public import OriginalUniformCowanReadQ0318
public import OriginalUniformCowanReadQ1318
public import OriginalUniformCowanReadKS318
public section
namespace OriginalUniformSparseJet318
open OriginalUniformCowanRead318
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
variable {K : Type*} [Field K]
@[expose] def H00 (s t : K) : K := (((-1) * (s^3) * (t^3)) + (4 * (s^2) * (t^3)) + (31 * (s^2) * (t^2)) + ((-1) * 10 * s * (t^2)) + ((-1) * 120 * s * t))
@[expose] def H02 (s t : K) : K := (((-1) * (s^3) * (t^5)) + ((-1) * 6 * (s^3) * (t^4)) + ((-1) * 4 * (s^2) * (t^4)) + (50 * (s^2) * (t^3)) + (105 * s * (t^3)) + ((-1) * 100 * s * (t^2)) + ((-1) * 300 * (t^2)))
@[expose] def H10 (s t : K) : K := (((s^4) * (t^2)) + (6 * (s^3) * (t^2)) + (9 * (s^3) * t) + ((-1) * 20 * (s^2) * t) + ((-1) * 60 * (s^2)))
@[expose] def H12 (s t : K) : K := (((s^4) * (t^4)) + ((-1) * 4 * (s^4) * (t^3)) + ((-1) * 36 * (s^3) * (t^3)) + (30 * (s^3) * (t^2)) + (275 * (s^2) * (t^2)) + ((-1) * 50 * (s^2) * t) + ((-1) * 600 * s * t))

@[expose] def ps (m p q R : K) : K := 2*R*p+(2*m*p-q)
@[expose] def pt (m p q R : K) : K := 2*R*p-(2*m*p-q)
@[expose] def V0 (m p q R : K) : K := H00 (m+R) (m-R)*ps m p q R + H10 (m+R) (m-R)*pt m p q R
@[expose] def V2 (m p q R : K) : K := H02 (m+R) (m-R)*ps m p q R + H12 (m+R) (m-R)*pt m p q R
@[expose] def factorA (n s t : K) : K := t^2*(n^2-31*n+120+(10-4*n)*t)*(n^2+9*n-60+(6*n-20)*s)
@[expose] def cross (m n : K) : K := n^4+2*m*n^3+4*n^3+168*m*n^2+421*n^2-1330*m*n-4010*n+2400*m+9000
@[expose] def delta (m n : K) : K := (n-5)*((n^2-5*n)*(2*m)+10*n^2-90*n+216)^2
@[expose] def detNumerator (m n p q R : K) : K := (2*n-3)*
  (factorA n (m+R) (m-R)*(ps m p q R)^2+factorA n (m-R) (m+R)*(pt m p q R)^2
    -2*n*cross m n*ps m p q R*pt m p q R)
theorem quaternion_remainder (m n p q a b T R : K) (hr : R^2=m^2-n) :
    -14*T*(a+b*R)^2*V0 m p q R - 42*V2 m p q R =
    28*lawQ0 m n p q a b T+R*28*lawQ1 m n p q a b T := by
  have h2 : R^2=m^2-n := hr
  have h3 : R^3=(m^2-n)^1*R := (pow_succ R 2).trans (congrArg (fun u : K => u*R) ((pow_mul R 2 1).trans (congrArg (fun u : K => u^1) hr)))
  have h5 : R^5=(m^2-n)^2*R := (pow_succ R 4).trans (congrArg (fun u : K => u*R) ((pow_mul R 2 2).trans (congrArg (fun u : K => u^2) hr)))
  have h4 : R^4=(m^2-n)^2 := (pow_mul R 2 2).trans (congrArg (fun u : K => u^2) hr)
  have h6 : R^6=(m^2-n)^3 := (pow_mul R 2 3).trans (congrArg (fun u : K => u^3) hr)
  have h7 : R^7=(m^2-n)^3*R := (pow_succ R 6).trans (congrArg (fun u : K => u*R) ((pow_mul R 2 3).trans (congrArg (fun u : K => u^3) hr)))
  have h8 : R^8=(m^2-n)^4 := (pow_mul R 2 4).trans (congrArg (fun u : K => u^4) hr)
  have h9 : R^9=(m^2-n)^4*R := (pow_succ R 8).trans (congrArg (fun u : K => u*R) ((pow_mul R 2 4).trans (congrArg (fun u : K => u^4) hr)))
  simp only [V0,V2,H00,H10,H02,H12,ps,pt,lawQ0,lawQ1]
  ring_nf
  simp only [h2,h3,h4,h5,h6,h7,h8,h9]
  ring
theorem ks_remainder (m n p q J X Y R : K) (hr : R^2=m^2-n) :
    detNumerator m n p q R * X * Y + 5040*J*(m^2-n)*n*delta m n = 4*lawKS m n p q J X Y := by
  have h2 : R^2=m^2-n := hr
  have h4 : R^4=(m^2-n)^2 := (pow_mul R 2 2).trans (congrArg (fun u : K => u^2) hr)
  have h6 : R^6=(m^2-n)^3 := (pow_mul R 2 3).trans (congrArg (fun u : K => u^3) hr)
  simp only [detNumerator,factorA,ps,pt,cross,delta,lawKS]
  ring_nf
  simp only [h2,h4,h6]
  ring
end OriginalUniformSparseJet318
#print axioms OriginalUniformSparseJet318.quaternion_remainder
#print axioms OriginalUniformSparseJet318.ks_remainder
