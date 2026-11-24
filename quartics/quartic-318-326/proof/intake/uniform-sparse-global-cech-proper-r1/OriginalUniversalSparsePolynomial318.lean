module
public import OriginalSeparableSexticJet318
public section
noncomputable section
namespace OriginalUniversalSparsePolynomial318
open Polynomial
variable {K : Type*} [CommRing K]
@[expose] def pol : List K → K[X]
  | [] => 0
  | h::l => C h + X*pol l
theorem pol_coeff (l : List K) (n : ℕ) : (pol l).coeff n=l[n]?.getD 0 := by
  induction l generalizing n with
  | nil => simp [pol]
  | cons c l ih =>
    cases n with
    | zero => simp [pol]
    | succ n => simp [pol,coeff_X_mul,ih]
theorem pol_bound (l : List K) (n : ℕ) (h : l.length ≤ n+1) : (pol l).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [pol_coeff,List.getElem?_eq_none (by omega)]
  rfl
@[expose] def cvec (s t : K) : List K :=
  let n := s*t; let w := 5-n
  [t^2*w^3, -2*n*t*w^2, 0, 10*n*w, 0, -2*n*s, s^2]
@[expose] def sextic (s t : K) : K[X] := pol (cvec s t)
@[expose] def gS (s t : K) : List K :=
  let n := s*t; let w := 5-n
  [-3*t^3*w^2,-2*t^2*w^2+4*n*t^2*w,0,10*t*(5-2*n),0,-4*s*t,2*s]
@[expose] def gT (s t : K) : List K :=
  let n := s*t; let w := 5-n
  [2*t*w^3-3*s*t^2*w^2,-4*s*t*w^2+4*n^2*w,0,10*s*(5-2*n),0,-2*s^2,0]
@[expose] def core (s t : K) : K :=
  let n:=s*t
  (n^2-5*n)*(s+t)+10*n^2-90*n+216
@[expose] def denom (s t : K) : K := -200000*s*t^3*(s*t-5)^4*core s t
@[expose] def jachead (s t : K) : K := 20000*s*t*(s*t-5)^2
theorem sextic_degree (s t : K) [IsDomain K] (hs : s≠0) : (sextic s t).natDegree=6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (pol_bound _ _ (by simp [cvec]))
  rw [pol_coeff]
  simpa [cvec] using pow_ne_zero 2 hs
theorem sextic_leading (s t : K) [IsDomain K] (hs : s≠0) : (sextic s t).leadingCoeff=s^2 := by
  rw [leadingCoeff, sextic_degree s t hs, sextic, pol_coeff]
  simp [cvec]
end OriginalUniversalSparsePolynomial318
