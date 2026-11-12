module
public import LiteralSievePolynomial318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace LiteralSecondSievePolynomial318
open MvPolynomial LiteralSievePolynomial318
set_option maxHeartbeats 2000000

/-- The actual rank-three polynomial is irreducible, proved as a primitive
linear polynomial in x with relatively prime coefficients in z,w. This
constructs the irreducibility needed by the second chart. -/
theorem secondP_irreducible (κ t : ℚ) (hκ : κ≠0) (ht2 : t+2≠0) :
    Irreducible (secondP κ t) := by
  let f : Poly := C (-2)*X 1
  let g : Poly := C (κ*(t+2))*X 2^2
  have hf : f≠0 := by
    intro hh
    have he := congrArg (eval (fun _ : Fin 3 => (1:ℚ))) hh
    norm_num [f] at he
  have hg : g≠0 := by
    intro hh
    have he := congrArg (eval (fun _ : Fin 3 => (1:ℚ))) hh
    have hz : κ*(t+2)=0 := by simpa [g] using he
    exact (mul_ne_zero hκ ht2) hz
  have hfv : f.vars⊆{1} := by
    simpa only [f,pow_one] using scaled_power_vars (-2) 1 1
  have hgv : g.vars⊆{2} := scaled_power_vars (κ*(t+2)) 2 2
  have hfg : IsRelPrime f g := by
    apply disjoint_vars_relPrime f g hf hg
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : i=1 := by simpa using hfv hi
    have hj' : i=2 := by simpa using hgv hj
    omega
  have hi := irreducible_mul_X_add f g (0:Fin 3) hf
    (by intro hh; have hx := hfv hh; norm_num at hx)
    (by intro hh; have hx := hgv hh; norm_num at hx) hfg
  have he : secondP κ t=f*X 0+g := by
    dsimp [secondP,f,g]
    push_cast
    ring
  rw [he]
  exact hi

/-- The constant term of K rules out divisibility by the homogeneous
irreducible second polynomial when t and t+2 are nonzero. -/
theorem second_pair_relPrime_regular (κ t : ℚ) (hκ : κ≠0)
    (ht : t≠0) (ht2 : t+2≠0) : IsRelPrime (secondP κ t) (normK κ t) := by
  apply (secondP_irreducible κ t hκ ht2).isRelPrime_iff_not_dvd.mpr
  rintro ⟨f,hf⟩
  have he := congrArg (eval (fun _ : Fin 3 => (0:ℚ))) hf
  have hz : (t^2+2*t)^2=0 := by simpa [secondP,normK] using he
  have ht' : t^2+2*t≠0 := by
    have hid : t^2+2*t=t*(t+2) := by ring
    rw [hid]
    exact mul_ne_zero ht ht2
  exact (pow_ne_zero 2 ht') hz

/-- Each coordinate variable is irreducible by its actual degree-one
coefficient1, not an imported geometric irreducibility assumption. -/
lemma coordinate_irreducible (i : Fin 3) : Irreducible (X i:Poly) := by
  apply irreducible_of_totalDegree_eq_one (by simp)
  intro a ha
  apply isUnit_iff_dvd_one.mpr
  simpa using ha (Finsupp.single i 1)

lemma first_coordinate_relPrime_exceptional (κ : ℚ) :
    IsRelPrime (X 0:Poly) (normK κ (-2)) := by
  apply (coordinate_irreducible 0).isRelPrime_iff_not_dvd.mpr
  rintro ⟨f,hf⟩
  have he := congrArg (eval (fun i : Fin 3 => if i=1 then (1:ℚ) else 0)) hf
  norm_num [normK] at he

lemma second_coordinate_relPrime_exceptional (κ : ℚ) :
    IsRelPrime (X 1:Poly) (normK κ (-2)) := by
  apply (coordinate_irreducible 1).isRelPrime_iff_not_dvd.mpr
  rintro ⟨f,hf⟩
  have he := congrArg (eval (fun i : Fin 3 => if i=0 then (1:ℚ) else 0)) hf
  norm_num [normK] at he

/-- The exceptional t=-2 chart is handled separately: Pprime=-2*x*z,
and neither coordinate factor divides the actual K. -/
theorem second_pair_relPrime_exceptional (κ : ℚ) :
    IsRelPrime (secondP κ (-2)) (normK κ (-2)) := by
  have hh := (first_coordinate_relPrime_exceptional κ).mul_left
    (second_coordinate_relPrime_exceptional κ)
  have hc : IsUnit (C (-2):Poly) :=
    (isUnit_iff_ne_zero.mpr (by norm_num : (-2:ℚ)≠0)).map C
  have he : secondP κ (-2)=C (-2)*(X 0*X 1) := by
    norm_num [secondP] <;> ring
  rw [he]
  exact (isRelPrime_mul_unit_left_left hc).mpr hh

/-- Full rational coprimality for the second original chart, including its
exceptional nonzero slice t=-2. -/
theorem second_pair_relPrime (κ t : ℚ) (hκ : κ≠0) (ht : t≠0) :
    IsRelPrime (secondP κ t) (normK κ t) := by
  by_cases ht2 : t+2=0
  · have he : t=-2 := by linarith
    rw [he]
    exact second_pair_relPrime_exceptional κ
  · exact second_pair_relPrime_regular κ t hκ ht ht2

end LiteralSecondSievePolynomial318
