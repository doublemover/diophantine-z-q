module
public import PurePowerReductionFiniteSpan318
public section
noncomputable section
namespace MonomialDegreeFiltration318
open PurePowerReductionFiniteSpan318
variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]

@[expose] def piece (x : ι → A) (n : ℕ) : Submodule R A :=
  Submodule.span R {y : A | ∃ d : ι → ℕ, weight d ≤ n ∧ monomial x d = y}

lemma mono (x : ι → A) {m n : ℕ} (h : m ≤ n) : piece (R:=R) x m ≤ piece x n := by
  apply Submodule.span_mono
  rintro y ⟨d,hd,rfl⟩
  exact ⟨d,hd.trans h,rfl⟩

lemma one_mem (x : ι → A) (n : ℕ) : (1:A) ∈ piece (R:=R) x n := by
  apply Submodule.subset_span
  exact ⟨0,by simp [weight],by simp [monomial]⟩

lemma scalar_mem (x : ι → A) (r : R) (n : ℕ) :
    algebraMap R A r ∈ piece x n := by
  simpa only [Algebra.smul_def,mul_one] using (piece x n).smul_mem r (one_mem x n)

lemma mul_mem (x : ι → A) {m n : ℕ} {a b : A}
    (ha : a ∈ piece (R:=R) x m) (hb : b ∈ piece (R:=R) x n) :
    a*b ∈ piece (R:=R) x (m+n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨d,hd,rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨e,he,rfl⟩ := hb
      exact Submodule.subset_span ⟨d+e,by rw [weight_add]; omega,monomial_add x d e⟩
    | zero => simpa only [mul_zero] using (piece (R:=R) x (m+n)).zero_mem
    | add b c hb hc hb' hc' => simpa only [mul_add] using (piece x (m+n)).add_mem hb' hc'
    | smul r b hb hb' => simpa only [mul_smul_comm] using (piece x (m+n)).smul_mem r hb'
  | zero => simpa only [zero_mul] using (piece (R:=R) x (m+n)).zero_mem
  | add a c ha hc ha' hc' => simpa only [add_mul] using (piece x (m+n)).add_mem ha' hc'
  | smul r a ha ha' => simpa only [smul_mul_assoc] using (piece x (m+n)).smul_mem r ha'

lemma pow_mem (x : ι → A) {m : ℕ} {a : A}
    (ha : a ∈ piece (R:=R) x m) (k : ℕ) : a^k ∈ piece (R:=R) x (m*k) := by
  induction k with
  | zero => simpa only [pow_zero,Nat.mul_zero] using one_mem (R:=R) x 0
  | succ k ih => simpa only [pow_succ,Nat.mul_succ] using mul_mem x ih ha

lemma generator_power_mem (x : ι → A) (i : ι) (M : ℕ) :
    x i ^ M ∈ piece (R:=R) x M := by
  apply Submodule.subset_span
  exact ⟨Pi.single i M,by rw [weight_single],monomial_single x i M⟩

/-- Subtracting a base scalar from a pure power does not alter its
highest total-degree part. The difference of the (k+1)-st powers has
degree at most M*k over the actual specified base. -/
lemma power_difference_mem (x : ι → A) (i : ι) (M : ℕ) (r : R) (k : ℕ) :
    (x i^M-algebraMap R A r)^(k+1) - (x i^M)^(k+1) ∈ piece x (M*k) := by
  let u := x i ^ M
  let a := u - algebraMap R A r
  have hu : u ∈ piece (R:=R) x M := generator_power_mem x i M
  have ha : a ∈ piece (R:=R) x M := (piece x M).sub_mem hu (scalar_mem x r M)
  change a^(k+1)-u^(k+1) ∈ piece x (M*k)
  induction k with
  | zero =>
    have heq : a^1-u^1 = -algebraMap R A r := by dsimp [a]; ring
    rw [heq,Nat.mul_zero]
    exact (piece x 0).neg_mem (scalar_mem x r 0)
  | succ k ih =>
    have hfirst : (a^(k+1)-u^(k+1))*u ∈ piece (R:=R) x (M*(k+1)) := by
      simpa only [Nat.mul_add,Nat.mul_one] using mul_mem x ih hu
    have hsecond : algebraMap R A r*a^(k+1) ∈ piece x (M*(k+1)) := by
      simpa only [zero_add] using mul_mem x (scalar_mem x r 0) (pow_mem x ha (k+1))
    have heq : a^(k+1+1)-u^(k+1+1) =
        (a^(k+1)-u^(k+1))*u-algebraMap R A r*a^(k+1) := by
      simp only [pow_succ]
      dsimp [a]
      ring
    rw [heq]
    exact (piece x (M*(k+1))).sub_mem hfirst hsecond
end MonomialDegreeFiltration318
