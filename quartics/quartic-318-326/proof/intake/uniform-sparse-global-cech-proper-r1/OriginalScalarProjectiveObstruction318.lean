module
public import OriginalPhysicalNaganoFourRoot318
public import Mathlib.Data.ZMod.Basic
public section
namespace OriginalScalarProjectiveObstruction318
open OriginalMarkedIntPolynomialCertificate318
@[expose] def homog {R : Type*} [CommRing R] (a b : R) : List ℤ → R
  | [] => 0
  | c :: l => (c : R)*b^l.length + a*homog a b l
theorem map_homog {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (l : List ℤ) : f (homog a b l)=homog (f a) (f b) l := by
  induction l with
  | nil => simp [homog]
  | cons c l ih => simp only [homog,map_add,map_mul,map_pow,map_intCast,ih]
theorem homog_subst {K : Type*} [Field K] (a b : K) (l : List ℤ) :
    b*homog (a*b) b l = b^l.length*horner a l := by
  induction l with
  | nil => simp [homog,horner]
  | cons c l ih =>
    simp only [List.length_cons,homog,horner,pow_succ]
    linear_combination a*b*ih
/-- A rootless homogeneous reduction excludes a rational square of any numerator/denominator size. -/
theorem no_rat_square (p : ℕ) (hne : (0:ZMod p)≠1) (l : List ℤ)
    (hc : ∀ u v : ZMod p, u≠0 ∨ v≠0 → homog (u^2) (v^2) l≠0)
    (x : ℚ) : horner (x^2) l≠0 := by
  intro hx
  let u := x.num
  let v : ℤ := x.den
  have hv : (v:ℚ) ≠ 0 := by dsimp [v]; exact_mod_cast x.den_nz
  have huv : x*(v:ℚ)=(u:ℚ) := by
    exact (eq_div_iff hv).1 (by simpa [u,v] using x.num_div_den.symm)
  have he := homog_subst (x^2) ((v:ℚ)^2) l
  rw [← mul_pow, huv, hx, mul_zero] at he
  have hQ : homog ((u:ℚ)^2) ((v:ℚ)^2) l = 0 := (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hv)
  have hZ : homog (u^2) (v^2) l = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [Int.cast_zero,← Int.coe_castRingHom, map_homog, map_pow] using hQ
  have hmod := congrArg (Int.castRingHom (ZMod p)) hZ
  simp only [map_homog,map_pow,map_zero,Int.coe_castRingHom] at hmod
  apply hc _ _ _ hmod
  have hcop := (Rat.isCoprime_num_den x).map (Int.castRingHom (ZMod p))
  by_contra! hh
  obtain ⟨s,t,hst⟩ := hcop
  change s*(u:ZMod p)+t*(v:ZMod p)=1 at hst
  apply hne; simpa only [hh.1,hh.2,mul_zero,add_zero] using hst
end OriginalScalarProjectiveObstruction318
#print axioms OriginalScalarProjectiveObstruction318.no_rat_square
