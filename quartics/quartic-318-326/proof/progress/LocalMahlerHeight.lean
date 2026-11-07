module
public import HeightCoverageFromMahler318
public import Mathlib.RingTheory.Polynomial.GaussNorm
public section
noncomputable section
namespace LocalMahlerHeight
open Polynomial NumberField HeightCoverageFromMahler318
set_option maxHeartbeats 0

lemma triple_bezout (a : ℕ) (b c : ℤ)
    (hg : Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1) :
    ∃ r s t : ℤ, r*(a:ℤ)+s*b+t*c=1 := by
  let d := Int.gcd (a:ℤ) b
  have hd : Int.gcd (d:ℤ) c = 1 := by simpa [d,Int.gcd_def] using hg
  have h1 := Int.gcd_eq_gcd_ab (a:ℤ) b
  have h2 := Int.gcd_eq_gcd_ab (d:ℤ) c
  rw [hd] at h2
  refine ⟨Int.gcdA (a:ℤ) b*Int.gcdA (d:ℤ) c,
    Int.gcdB (a:ℤ) b*Int.gcdA (d:ℤ) c,Int.gcdB (d:ℤ) c,?_⟩
  dsimp only [d] at *
  linear_combination -h2 - Int.gcdA (↑((a:ℤ).gcd b)) c*h1

variable {F : Type*} [Field F] [NumberField F]

lemma finite_integer_le_one (v : FinitePlace F) (n : ℤ) : v (n:F) ≤ 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  exact hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)

lemma finite_primitive_gauss (v : FinitePlace F) (a : ℕ) (b c : ℤ)
    (hg : Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1) :
    ((quadratic a b c).map (Int.castRingHom F)).gaussNorm v.val 1=1 := by
  let p := (quadratic a b c).map (Int.castRingHom F)
  have hu : p.gaussNorm v.val 1 ≤ 1 := by
    obtain ⟨i,hi⟩ := p.exists_eq_gaussNorm v.val 1
    rw [hi]
    simpa [p,coeff_map,←FinitePlace.coe_apply] using finite_integer_le_one v ((quadratic a b c).coeff i)
  have hca : (quadratic a b c).coeff 2=(a:ℤ) := by
    simp only [quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  have hcb : (quadratic a b c).coeff 1=b := by
    simp only [quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  have hcc : (quadratic a b c).coeff 0=c := by
    simp only [quadratic,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  have ha : v (a:F) ≤ p.gaussNorm v.val 1 := by
    simpa only [p,coeff_map,hca,Int.coe_castRingHom,Int.cast_natCast,one_pow,mul_one,←FinitePlace.coe_apply] using
      p.le_gaussNorm v.val (by norm_num : (0:ℝ)≤1) 2
  have hb : v (b:F) ≤ p.gaussNorm v.val 1 := by
    simpa only [p,coeff_map,hcb,Int.coe_castRingHom,one_pow,mul_one,←FinitePlace.coe_apply] using
      p.le_gaussNorm v.val (by norm_num : (0:ℝ)≤1) 1
  have hc : v (c:F) ≤ p.gaussNorm v.val 1 := by
    simpa only [p,coeff_map,hcc,Int.coe_castRingHom,one_pow,mul_one,←FinitePlace.coe_apply] using
      p.le_gaussNorm v.val (by norm_num : (0:ℝ)≤1) 0
  obtain ⟨r,s,t,h⟩ := triple_bezout a b c hg
  have hF : (r:F)*(a:F)+(s:F)*(b:F)+(t:F)*(c:F)=1 := by exact_mod_cast h
  have hfirst := FinitePlace.add_le v ((r:F)*(a:F)) ((s:F)*(b:F))
  have hlast := FinitePlace.add_le v ((r:F)*(a:F)+(s:F)*(b:F)) ((t:F)*(c:F))
  rw [hF,map_one] at hlast
  rw [map_mul,map_mul] at hfirst
  rw [map_mul] at hlast
  have hr := (mul_le_of_le_one_left (apply_nonneg v (a:F)) (finite_integer_le_one v r)).trans ha
  have hs := (mul_le_of_le_one_left (apply_nonneg v (b:F)) (finite_integer_le_one v s)).trans hb
  have ht := (mul_le_of_le_one_left (apply_nonneg v (c:F)) (finite_integer_le_one v t)).trans hc
  exact le_antisymm hu (hlast.trans (max_le (hfirst.trans (max_le hr hs)) ht))

lemma linear_gauss (v : FinitePlace F) (x : F) :
    (X-C x).gaussNorm v.val 1=max (v x) 1 := by
  apply le_antisymm
  · obtain ⟨i,hi⟩ := (X-C x).exists_eq_gaussNorm v.val 1
    rw [hi]
    by_cases h0 : i=0
    · subst i; simpa only [coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,map_neg_eq_map,one_pow,mul_one,←FinitePlace.coe_apply] using le_max_left (v x) 1
    · by_cases h1 : i=1
      · subst i; simp
      · simp [coeff_sub,coeff_X,coeff_C,h0,Ne.symm h1]
  · apply max_le
    · have h := (X-C x).le_gaussNorm v.val (by norm_num : (0:ℝ)≤1) 0
      simp only [coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub,map_neg_eq_map,one_pow,mul_one] at h
      simpa only [FinitePlace.coe_apply] using h
    · have h := (X-C x).le_gaussNorm v.val (by norm_num : (0:ℝ)≤1) 1
      simpa only [coeff_sub,coeff_X_one,coeff_C,ite_false,one_ne_zero,sub_zero,map_one,one_pow,mul_one] using h

/-- The exact normalized finite-place factor in the primitive quadratic
Mahler/height identity, proved using actual number-field finite places. -/
lemma finite_roots_product (v : FinitePlace F) (a : ℕ) (b c : ℤ) (x y : F)
    (hg : Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1)
    (hfactor : (quadratic a b c).map (Int.castRingHom F) = C (a:F)*((X-C x)*(X-C y))) :
    v (a:F)*max (v x) 1*max (v y) 1=1 := by
  have h := finite_primitive_gauss v a b c hg
  rw [hfactor,Polynomial.gaussNorm_mul (FinitePlace.add_le v) (by norm_num),
    Polynomial.gaussNorm_mul (FinitePlace.add_le v) (by norm_num),
    Polynomial.gaussNorm_C,linear_gauss,linear_gauss] at h
  simpa only [mul_assoc,←FinitePlace.coe_apply] using h

#print axioms triple_bezout
#print axioms finite_integer_le_one
#print axioms finite_primitive_gauss
#print axioms linear_gauss
#print axioms finite_roots_product
end LocalMahlerHeight
