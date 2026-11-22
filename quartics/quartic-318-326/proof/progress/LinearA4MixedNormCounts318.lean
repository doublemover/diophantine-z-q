module
public import LinearA4GaussianCounts318
public section
noncomputable section

namespace LinearA4MixedNormCounts318
open LinearA4GaussianCounts318
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev Box (K : Type*) := Plane K × Plane K
def coeffNorm (c : K × K) (z : Box K) : K := c.1*LinearA4GaussianCounts318.norm z.1+c.2*LinearA4GaussianCounts318.norm z.2
def zeroSize (K : Type*) [Field K] [Fintype K] [DecidableEq K] : ℤ :=
  size K+(size K-1)*χ K
def mixedSize (K : Type*) [Fintype K] : ℤ := (size K)^3+(size K)^2-size K

/- Common fibre of two independent norm equations. The same fibre appears
for every distinct pair, so the union can later be counted exactly. -/
omit [Fintype K] [DecidableEq K] in
theorem simultaneous_iff (c d : K × K) (h : c.1*d.2 - d.1*c.2 ≠ 0) (z : Box K) :
    coeffNorm c z=0 ∧ coeffNorm d z=0 ↔ LinearA4GaussianCounts318.norm z.1=0 ∧ LinearA4GaussianCounts318.norm z.2=0 := by
  constructor
  · rintro ⟨hc,hd⟩
    unfold coeffNorm at hc hd
    have x : (c.1*d.2-d.1*c.2)*LinearA4GaussianCounts318.norm z.1=0 := by linear_combination d.2*hc-c.2*hd
    have y : (c.1*d.2-d.1*c.2)*LinearA4GaussianCounts318.norm z.2=0 := by linear_combination c.1*hd-d.1*hc
    exact ⟨(mul_eq_zero.mp x).resolve_left h,(mul_eq_zero.mp y).resolve_left h⟩
  · rintro ⟨hx,hy⟩
    simp [coeffNorm,hx,hy]

/-- A joint fibre is exactly a product of the two binary fibres. -/
def pairedFibres (r s : K) :
    {z : Box K // LinearA4GaussianCounts318.norm z.1=r ∧ LinearA4GaussianCounts318.norm z.2=s} ≃ Fibre LinearA4GaussianCounts318.norm r × Fibre LinearA4GaussianCounts318.norm s where
  toFun z := (⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩)
  invFun z := ⟨(z.1.val,z.2.val),z.1.property,z.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rankTwoLeft (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    fibreSize (coeffNorm ((1,0):K × K)) 0=zeroSize K*(size K)^2 := by
  let e : Fibre (coeffNorm ((1,0):K × K)) 0 ≃ Fibre LinearA4GaussianCounts318.norm (0:K) × Plane K :=
    ⟨fun z => (⟨z.val.1,by simpa only [coeffNorm,one_mul,zero_mul,add_zero] using z.property⟩,z.val.2),
      fun z => ⟨(z.1.val,z.2),by simpa only [coeffNorm,one_mul,zero_mul,add_zero] using z.1.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  rw [fibreSize,Fintype.card_congr e,Fintype.card_prod,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  change fibreSize LinearA4GaussianCounts318.norm (0:K)*(size K*size K)=_
  rw [norm_count hp h2]
  simp only [ite_true,zeroSize,pow_two]

theorem rankTwoRight (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    fibreSize (coeffNorm ((0,1):K × K)) 0=zeroSize K*(size K)^2 := by
  let e : Fibre (coeffNorm ((0,1):K × K)) 0 ≃ Fibre (coeffNorm ((1,0):K × K)) 0 :=
    ⟨fun z => ⟨(z.val.2,z.val.1),by simpa only [coeffNorm,one_mul,zero_mul,zero_add,add_zero] using z.property⟩,
      fun z => ⟨(z.val.2,z.val.1),by simpa only [coeffNorm,one_mul,zero_mul,zero_add,add_zero] using z.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  exact (congrArg (fun n : ℕ => (n:ℤ)) (Fintype.card_congr e)).trans (rankTwoLeft hp h2)

/-- Direct dependent partition indexed by the actual first norm. Every
remaining linear form has both coefficients nonzero at the good primes. -/
def mixedFibres (a b : K) (hb : b≠0) :
    Fibre (coeffNorm (a,b)) 0 ≃ (Σ r : K, Fibre LinearA4GaussianCounts318.norm r × Fibre LinearA4GaussianCounts318.norm (-a*r/b)) where
  toFun z := ⟨LinearA4GaussianCounts318.norm z.val.1,⟨z.val.1,rfl⟩,⟨z.val.2,by
    apply (eq_div_iff hb).2
    have h := z.property
    change a*LinearA4GaussianCounts318.norm z.val.1 + b*LinearA4GaussianCounts318.norm z.val.2=0 at h
    linear_combination h⟩⟩
  invFun t := ⟨(t.2.1.val,t.2.2.val),by
    change a*LinearA4GaussianCounts318.norm t.2.1.val+b*LinearA4GaussianCounts318.norm t.2.2.val=0
    rw [t.2.1.property,t.2.2.property]
    field_simp [hb]
    ring⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨r,⟨u,hu⟩,⟨v,hv⟩⟩
    subst r
    rfl

/-- Rank four: p³+p²−p for all allowed nonzero coefficient pairs.
In particular the split/inert correction does not occur on these forms. -/
theorem rankFour (hp : ringChar K≠2) (h2 : (2:K)≠0)
    {a b : K} (ha : a≠0) (hb : b≠0) :
    fibreSize (coeffNorm (a,b)) 0=mixedSize K := by
  have H : fibreSize (coeffNorm (a,b)) 0 =
      ∑ r : K, fibreSize LinearA4GaussianCounts318.norm r * fibreSize LinearA4GaussianCounts318.norm (-a*r/b) := by
    rw [fibreSize,Fintype.card_congr (mixedFibres a b hb),Fintype.card_sigma,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fintype.card_prod,Nat.cast_mul]
    rfl
  rw [H,sum_split_zero _ ((size K-χ K)^2)]
  · simp only [mul_zero,zero_div,norm_count hp h2,ite_true]
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) with hs|hi
    · change χ K=1 at hs
      simp only [hs,mixedSize]
      ring
    · change χ K= -1 at hi
      simp only [hi,mixedSize]
      ring
  · intro r hr
    have hs : -a*r/b≠0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) hr) hb
    simp only [norm_count hp h2,hr,hs,ite_false,pow_two]

theorem joint_count (hp : ringChar K≠2) (h2 : (2:K)≠0) :
    (Fintype.card {z : Box K // LinearA4GaussianCounts318.norm z.1=(0:K) ∧ LinearA4GaussianCounts318.norm z.2=0}:ℤ)=(zeroSize K)^2 := by
  rw [Fintype.card_congr (pairedFibres (0:K) 0),Fintype.card_prod,Nat.cast_mul]
  change fibreSize LinearA4GaussianCounts318.norm (0:K)*fibreSize LinearA4GaussianCounts318.norm (0:K)=_
  simp only [norm_count hp h2,ite_true,zeroSize,pow_two]

/- In the original two observations (u+kQ²q,u+lQ²q), the residual
slope coefficients are the interpolation pair l−m,m−k divided by l−k. -/
omit [Fintype K] [DecidableEq K] in
theorem interpolation (u v k l m : K) (h : l-k≠0) :
    ((l-m)/(l-k))*(u+k*v)+((m-k)/(l-k))*(u+l*v)=u+m*v := by
  field_simp [h]
  ring

omit [Fintype K] [DecidableEq K] in
theorem interpolation_det (k l m n : K) (h : l-k≠0) :
    ((l-m)/(l-k))*((n-k)/(l-k))-((l-n)/(l-k))*((m-k)/(l-k))=(n-m)/(l-k) := by
  field_simp [h]
  ring

end LinearA4MixedNormCounts318
