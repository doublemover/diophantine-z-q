module
public import GaussianRayQuarterPreparation318
public section
noncomputable section
namespace GaussianNeighborNorms318
set_option maxHeartbeats 1000000

@[expose] def norm (a b : ℤ) : ℕ := a.natAbs^2+b.natAbs^2
@[expose] def minus (a b : ℤ) : ℕ := norm (a-1) b
@[expose] def plus (a b : ℤ) : ℕ := norm (a+1) b

lemma norm_cast (a b : ℤ) : (norm a b:ℤ)=a^2+b^2 := by
  simp only [norm,Nat.cast_add,Nat.cast_pow,Int.natCast_natAbs,sq_abs]

/-- The actual signed ray gives exact valuations six and two of the two
neighboring Gaussian norms. The odd factors are genuine natural numbers. -/
theorem ray_factors (a b : ℤ) (ha : a%16=9) (hb : b%16=0) :
    ∃ m n : ℕ, Odd m ∧ Odd n ∧ minus a b=64*m ∧ plus a b=4*n := by
  let A := a/16
  let B := b/16
  have ha' : a=9+16*A := by dsimp [A]; omega
  have hb' : b=16*B := by dsimp [B]; omega
  let M : ℤ := (1+2*A)^2+4*B^2
  let N : ℤ := (5+8*A)^2+64*B^2
  have hM : 0≤M := by dsimp [M]; positivity
  have hN : 0≤N := by dsimp [N]; positivity
  have hMo : M%2=1 := by norm_num [M,Int.add_emod,Int.mul_emod,Int.pow_emod]
  have hNo : N%2=1 := by norm_num [N,Int.add_emod,Int.mul_emod,Int.pow_emod]
  have hmc : (M.toNat:ℤ)=M := Int.toNat_of_nonneg hM
  have hnc : (N.toNat:ℤ)=N := Int.toNat_of_nonneg hN
  have hm : Odd M.toNat := by
    refine ⟨M.toNat/2,?_⟩
    have he : M.toNat%2=1 := by exact_mod_cast (show (M.toNat:ℤ)%2=1 by rwa [hmc])
    omega
  have hn : Odd N.toNat := by
    refine ⟨N.toNat/2,?_⟩
    have he : N.toNat%2=1 := by exact_mod_cast (show (N.toNat:ℤ)%2=1 by rwa [hnc])
    omega
  refine ⟨M.toNat,N.toNat,hm,hn,?_,?_⟩
  · have he : (minus a b:ℤ)=64*(M.toNat:ℤ) := by
      rw [minus,norm_cast,hmc,ha',hb']
      dsimp [M]
      ring
    exact_mod_cast he
  · have he : (plus a b:ℤ)=4*(N.toNat:ℤ) := by
      rw [plus,norm_cast,hnc,ha',hb']
      dsimp [N]
      ring
    exact_mod_cast he

lemma odd_pos {n : ℕ} (hn : Odd n) : 0<n := by rcases hn with ⟨k,hk⟩; omega

theorem quarters (a b : ℤ) (ha : a%16=9) (hb : b%16=0) :
    0<minus a b/4 ∧ 0<plus a b/4 ∧ 16∣minus a b/4 ∧ Odd (plus a b/4) ∧
      ∃ m : ℕ, Odd m ∧ minus a b/4=16*m := by
  obtain ⟨m,n,hm,hn,hminus,hplus⟩ := ray_factors a b ha hb
  have hmpos := odd_pos hm
  have hnpos := odd_pos hn
  have hqm : minus a b/4=16*m := by omega
  have hqp : plus a b/4=n := by omega
  rw [hqm,hqp]
  exact ⟨by positivity,hnpos,dvd_mul_right _ _,hn,m,hm,rfl⟩

/-- Dividing BOTH actual neighboring norms by four removes exactly the
common factor four, rather than silently asserting coprimality. -/
theorem quarter_coprime (a b c d : ℤ)
    (ha : a%16=9) (hb : b%16=0) (hc : c%16=9) (hd : d%16=0)
    (hg : Nat.gcd (minus a b) (plus c d)=4) :
    Nat.Coprime (minus a b/4) (plus c d/4) := by
  obtain ⟨m,n,hm,hn,he,hf⟩ := ray_factors a b ha hb
  obtain ⟨m',n',hm',hn',he',hf'⟩ := ray_factors c d hc hd
  have hqm : minus a b/4=16*m := by omega
  have hqp : plus c d/4=n' := by omega
  rw [hqm,hqp]
  have hfour : minus a b=4*(16*m) := by omega
  have hh := hg
  rw [hfour,hf',Nat.gcd_mul_left] at hh
  change Nat.gcd (16*m) n'=1
  omega

/-- Exact neighboring-norm error around the original rational prime. -/
lemma neighbor_errors (p : ℕ) (a b : ℤ) (hp : (p:ℤ)=a^2+b^2) :
    (minus a b:ℤ)-(p:ℤ)=1-2*a ∧ (plus a b:ℤ)-(p:ℤ)=1+2*a := by
  simp only [minus,plus,norm_cast,hp]
  constructor <;> ring

end GaussianNeighborNorms318
