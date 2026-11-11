module
public import SelectedQuarterOrder318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public section
noncomputable section
namespace FiniteRayRootAlgebra318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma square_of_period (x : ZMod p) (n : ℕ) (hn : n≠0) (hpow : x^n=1)
    (hd : n∣p/2) : IsSquare x := by
  have hx : x≠0 := by intro he; rw [he,zero_pow hn] at hpow; exact zero_ne_one hpow
  apply (ZMod.euler_criterion p hx).mpr
  obtain ⟨k,hk⟩ := hd
  rw [hk,pow_mul,hpow,one_pow]

/-- Construct the exact root z^8=−1 from p≡1 mod16 using only quadratic
Euler criteria; no implicit choice of a primitive finite-field generator. -/
theorem eighth_root_neg_one (hmod : p%16=1) : ∃ z : ZMod p, z^8= -1 := by
  have hp4 : p%4≠3 := by omega
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr hp4
  have hi2 : i^2= -1 := by simpa only [pow_two] using hi.symm
  have hi4 : i^4=1 := by calc
    i^4=(i^2)^2 := by ring
    _ = 1 := by rw [hi2]; norm_num
  have hd4 : 4∣p/2 := ⟨2*(p/16),by omega⟩
  obtain ⟨j,hj⟩ := square_of_period p i 4 (by decide) hi4 hd4
  have hj2 : j^2=i := by simpa only [pow_two] using hj.symm
  have hj8 : j^8=1 := by calc
    j^8=(j^2)^4 := by ring
    _ = 1 := by rw [hj2,hi4]
  have hd8 : 8∣p/2 := ⟨p/16,by omega⟩
  obtain ⟨z,hz⟩ := square_of_period p j 8 (by decide) hj8 hd8
  have hz2 : z^2=j := by simpa only [pow_two] using hz.symm
  refine ⟨z,?_⟩
  calc
    z^8=((z^2)^2)^2 := by ring
    _ = -1 := by rw [hz2,hj2,hi2]

/-- The two ordinary quadratic-residue conclusions in the Gaussian ray
argument imply the precise quartic Euler condition for2. -/
theorem quartic_euler (hmod : p%16=1) (a b : ZMod p)
    (ha0 : a≠0) (hs0 : a+b≠0) (hnorm : a^2+b^2=0)
    (ha : IsSquare a) (hs : IsSquare (a+b)) : (2:ZMod p)^(p/4)=1 := by
  let i := b/a
  have hi2 : i^2= -1 := by
    dsimp [i]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 ha0)).mpr
    linear_combination hnorm
  have hi4 : i^4=1 := by calc
    i^4=(i^2)^2 := by ring
    _ = 1 := by rw [hi2]; norm_num
  have hquarter : p/4=4*(p/16) := by omega
  have hipow : i^(p/4)=1 := by rw [hquarter,pow_mul,hi4,one_pow]
  have hhalf : p/2=2*(p/4) := by omega
  have hae := (ZMod.euler_criterion p ha0).mp ha
  have hse := (ZMod.euler_criterion p hs0).mp hs
  have hai : a*i=b := by dsimp [i]; field_simp [ha0]
  have hformula : (a+b)^2=2*a^2*i := by
    calc
      (a+b)^2=2*a*b := by linear_combination hnorm
      _ = 2*a^2*i := by rw [←hai]; ring
  have he := congrArg (fun x : ZMod p => x^(p/4)) hformula
  simp only [mul_pow,←pow_mul] at he
  simp only [←hhalf,hse,hae,hipow,mul_one] at he
  exact he.symm

theorem fourth_root_two (hmod : p%16=1) (hpow : (2:ZMod p)^(p/4)=1) :
    ∃ t : ZMod p, t^4=2 := by
  have hp : p≠2 := by omega
  obtain ⟨r,hr⟩ := (ZMod.exists_sq_eq_two_iff hp).mpr (Or.inl (by omega))
  have hr2 : r^2=2 := by simpa only [pow_two] using hr.symm
  have hr0 : r≠0 := by
    intro he
    rw [he,zero_pow (by decide : (2:ℕ)≠0)] at hr2
    exact GoodReductionResidue318.two_residue_ne p hp hr2.symm
  have hs : IsSquare r := (ZMod.euler_criterion p hr0).mpr (by
    rw [show p/2=2*(p/4) by omega,pow_mul,hr2,hpow])
  obtain ⟨t,ht⟩ := hs
  have ht2 : t^2=r := by simpa only [pow_two] using ht.symm
  refine ⟨t,?_⟩
  calc
    t^4=(t^2)^2 := by ring
    _ = 2 := by rw [ht2,hr2]

end FiniteRayRootAlgebra318
