module
public import QuadraticDiscriminant318
public section
namespace PrimitiveQuadratic318
open ConcreteG8Domain
open scoped QuadraticAlgebra
set_option maxHeartbeats 0

lemma primitive_triple (a : ℕ) (b c : ℤ) (ha : 0<a) :
    ∃ (A g : ℕ) (B C : ℤ), 0<A ∧ 0<g ∧ a=g*A ∧ b=(g:ℤ)*B ∧ c=(g:ℤ)*C ∧
      Nat.gcd (Nat.gcd A B.natAbs) C.natAbs=1 := by
  let g := Nat.gcd (Nat.gcd a b.natAbs) c.natAbs
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ ha)
  have hga : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b.natAbs := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgc : g ∣ c.natAbs := Nat.gcd_dvd_right _ _
  have hgbz : (g:ℤ) ∣ b := by simpa using Int.natAbs_dvd_natAbs.mp hgb
  have hgcz : (g:ℤ) ∣ c := by simpa using Int.natAbs_dvd_natAbs.mp hgc
  refine ⟨a/g,g,b/g,c/g,Nat.div_pos (Nat.le_of_dvd ha hga) hg,hg,?_,?_,?_,?_⟩
  · exact (Nat.mul_div_cancel' hga).symm
  · exact (Int.mul_ediv_cancel' hgbz).symm
  · exact (Int.mul_ediv_cancel' hgcz).symm
  · simp only [Int.natAbs_ediv,Int.natAbs_natCast,hgbz,hgcz,or_true,ite_true,add_zero]
    rw [Nat.gcd_div hga hgb,Nat.gcd_div (Nat.gcd_dvd_left _ _) hgc]
    exact Nat.div_self hg

lemma cleared_quadratic (u v : ℚ) :
    ∃ (a : ℕ) (b c : ℤ), 0<a ∧
      (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 := by
  let d : ℕ := u.den*v.den
  let U : ℤ := u.num*(v.den:ℤ)
  let V : ℤ := v.num*(u.den:ℤ)
  have hd : 0<d := Nat.mul_pos u.den_pos v.den_pos
  have hu : (d:ℚ)*u=(U:ℚ) := by
    dsimp [d,U]
    push_cast
    linear_combination (v.den:ℚ)*u.den_mul_eq_num
  have hv : (d:ℚ)*v=(V:ℚ) := by
    dsimp [d,V]
    push_cast
    linear_combination (u.den:ℚ)*v.den_mul_eq_num
  refine ⟨d^2,-2*U*d,U^2-2*V^2,pow_pos hd _,?_⟩
  ext <;> norm_num [pair,pow_succ]
  · linear_combination ((d:ℚ)*u-(U:ℚ))*hu+2*((d:ℚ)*v+(V:ℚ))*hv
  · linear_combination 2*(d:ℚ)*v*hu

lemma primitive_defining_quadratic (u v : ℚ) :
    ∃ (a : ℕ) (b c : ℤ), 1≤a ∧ Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1 ∧
      (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 := by
  obtain ⟨a,b,c,ha,hp⟩ := cleared_quadratic u v
  obtain ⟨A,g,B,C,hA,hg,hea,heb,hec,hprim⟩ := primitive_triple a b c ha
  refine ⟨A,B,C,hA,hprim,?_⟩
  have hg0 : (g:K)≠0 := by exact_mod_cast hg.ne'
  apply (mul_eq_zero.mp (show (g:K)*((A:K)*(pair u v)^2+(B:K)*(pair u v)+(C:K))=0 from ?_)).resolve_left hg0
  rw [hea,heb,hec] at hp
  push_cast at hp
  linear_combination hp

lemma primitive_defining_quadratic_discriminant (u v : ℚ) (hv:v≠0) :
    ∃ (a : ℕ) (b c : ℤ) (k : ℕ), 1≤a ∧ 1≤k ∧
      Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1 ∧
      (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0 ∧
      b^2-4*(a:ℤ)*c=2*(k:ℤ)^2 := by
  obtain ⟨a,b,c,ha,hg,hp⟩ := primitive_defining_quadratic u v
  obtain ⟨k,hk,hd⟩ := QuadraticDiscriminant318.actual_root_discriminant (a:ℤ) b c u v
    (by omega) hv (by simpa using hp)
  exact ⟨a,b,c,k,ha,hk,hg,hp,hd⟩

#print axioms primitive_triple
#print axioms cleared_quadratic
#print axioms primitive_defining_quadratic
#print axioms primitive_defining_quadratic_discriminant
end PrimitiveQuadratic318
