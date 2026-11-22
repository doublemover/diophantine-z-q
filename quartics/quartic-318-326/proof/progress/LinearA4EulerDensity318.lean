module
public import LinearA4MixedNormCounts318
import all LinearA4MixedNormCounts318
public section
noncomputable section

namespace LinearA4EulerDensity318
open LinearA4GaussianCounts318 LinearA4MixedNormCounts318
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The residual mixed forms are indexed separately from the two observed
norms. Cardinality of this parameter is r−2, not r. -/
def coefficients {ι : Type*} (mix : ι → K × K) : (Fin 2 ⊕ ι) → K × K
  | .inl i => if i=0 then (1,0) else (0,1)
  | .inr i => mix i

def fibreSet (c : K × K) : Finset (Box K) := Finset.univ.filter (fun z => coeffNorm c z=0)
def joint : Finset (Box K) := Finset.univ.filter (fun z => LinearA4GaussianCounts318.norm z.1=0 ∧ LinearA4GaussianCounts318.norm z.2=0)
def badResidues {ι : Type*} [Fintype ι] [DecidableEq ι] (mix : ι → K × K) : Finset (Box K) :=
  Finset.univ.biUnion (fun i => fibreSet (coefficients mix i))

/-- All pair intersections equal one common core. Removing it once from
each fibre leaves honest disjoint residual sets, no quadratic error bound. -/
theorem union_core {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Type*} [DecidableEq X] (sets : ι → Finset X) (core : Finset X)
    (inc : ∀ i, core ⊆ sets i)
    (overlap : ∀ i j, i≠j → ∀ x∈sets i, x∈sets j → x∈core) :
    ((Finset.univ.biUnion sets).card:ℤ) =
      (∑ i, ((sets i).card:ℤ)) - ((Fintype.card ι:ℤ)-1)*(core.card:ℤ) := by
  classical
  let tail i := sets i \ core
  have pw : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint tail := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    obtain ⟨hi',hn⟩ := Finset.mem_sdiff.mp hi
    exact hn (overlap i j hij x hi' (Finset.mem_sdiff.mp hj).1)
  have dj : Disjoint core (Finset.univ.biUnion tail) := by
    apply Finset.disjoint_left.mpr
    intro x hcore htail
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp htail
    exact (Finset.mem_sdiff.mp hi).2 hcore
  have eq : Finset.univ.biUnion sets = core ∪ Finset.univ.biUnion tail := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union]
    constructor
    · rintro ⟨i,hi⟩
      by_cases h : x∈core
      · exact Or.inl h
      · exact Or.inr ⟨i,Finset.mem_sdiff.mpr ⟨hi,h⟩⟩
    · rintro (h|⟨i,hi⟩)
      · let i := Classical.choice (inferInstance : Nonempty ι)
        exact ⟨i,inc i h⟩
      · exact ⟨i,(Finset.mem_sdiff.mp hi).1⟩
  have tc (i : ι) : ((tail i).card:ℤ)=((sets i).card:ℤ)-(core.card:ℤ) := by
    have hn := Finset.card_sdiff_add_card_eq_card (inc i)
    change (tail i).card+core.card=(sets i).card at hn
    exact eq_sub_of_add_eq (by exact_mod_cast hn)
  rw [eq,Finset.card_union_of_disjoint dj,Finset.card_biUnion pw,Nat.cast_add,Nat.cast_sum]
  simp only [tc,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- Exact local count before taking the Euler product, from the actual two
rank-2 and m rank-4 residue forms. -/
theorem bad_count {ι : Type*} [Fintype ι] [DecidableEq ι] (mix : ι → K × K)
    (hp : ringChar K≠2) (h2 : (2:K)≠0)
    (both : ∀ i, (mix i).1≠0 ∧ (mix i).2≠0)
    (indep : ∀ i j, i≠j →
      (coefficients mix i).1*(coefficients mix j).2 -
      (coefficients mix j).1*(coefficients mix i).2≠0) :
    ((badResidues mix).card:ℤ) =
      2*zeroSize K*(size K)^2+(Fintype.card ι:ℤ)*mixedSize K -
        ((Fintype.card ι:ℤ)+1)*(zeroSize K)^2 := by
  have fiber (c : K × K) : ((fibreSet c).card:ℤ)=fibreSize (coeffNorm c) 0 := by
    simp only [fibreSize,Fintype.card_subtype,fibreSet]
  have core : ((joint : Finset (Box K)).card:ℤ)=(zeroSize K)^2 := by
    simpa only [joint,Fintype.card_subtype] using joint_count hp h2
  have inc (i : Fin 2 ⊕ ι) : (joint : Finset (Box K)) ⊆ fibreSet (coefficients mix i) := by
    intro z hz
    obtain ⟨h₁,h₂⟩ : LinearA4GaussianCounts318.norm z.1=0 ∧ LinearA4GaussianCounts318.norm z.2=0 := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [coeffNorm,h₁,h₂]⟩
  have inter (i j : Fin 2 ⊕ ι) (hne : i≠j) (z : Box K)
      (hi : z∈fibreSet (coefficients mix i)) (hj : z∈fibreSet (coefficients mix j)) :
      z∈(joint : Finset (Box K)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (simultaneous_iff _ _ (indep i j hne) z).mp ⟨(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2⟩⟩
  have sum : (∑ i : Fin 2 ⊕ ι, ((fibreSet (coefficients mix i)).card:ℤ)) =
      2*zeroSize K*(size K)^2+(Fintype.card ι:ℤ)*mixedSize K := by
    rw [Fintype.sum_sum_type]
    have l : (∑ i : Fin 2, ((fibreSet (coefficients mix (.inl i))).card:ℤ)) =
        2*zeroSize K*(size K)^2 := by
      rw [Fin.sum_univ_two,fiber,fiber]
      simp only [coefficients,ite_true,show (1:Fin 2)≠0 by decide,ite_false,rankTwoLeft hp h2,rankTwoRight hp h2]
      ring
    have r : (∑ i : ι, ((fibreSet (coefficients mix (.inr i))).card:ℤ)) =
        (Fintype.card ι:ℤ)*mixedSize K := by
      calc
        _ = ∑ _i : ι, mixedSize K := by
          apply Finset.sum_congr rfl
          intro i _
          rw [fiber]
          exact rankFour hp h2 (both i).1 (both i).2
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [l,r]
  unfold badResidues
  rw [union_core _ _ inc inter,sum,core,Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
  push_cast
  ring

/-- The local Euler factor uses this density g, not independent prime
probabilities on the four Gaussian coordinates. The explicit tail bound
is uniform under omission of the distinguished collision prime elsewhere. -/
theorem density_error (p m χ g : ℝ) (hp : 1≤p) (hm : 0≤m)
    (hχ : χ=1 ∨ χ= -1)
    (hg : g=(2*(p+(p-1)*χ)*p^2 + m*(p^3+p^2-p) -
      (m+1)*(p+(p-1)*χ)^2)/p^4) :
    |g-(m+2+2*χ)/p| ≤ (5*m+6)/p^2 := by
  have pp : 0 < p := by linarith
  have p₀ : p≠0 := pp.ne'
  have he : g-(m+2+2*χ)/p =
      (-2*χ*p^2+m*(p^2-p)-(m+1)*(p+(p-1)*χ)^2)/p^4 := by
    rw [hg]
    field_simp [p₀]
    ring
  rw [he,abs_div,abs_of_pos (pow_pos pp 4)]
  apply (div_le_iff₀ (pow_pos pp 4)).2
  have rhs : (5*m+6)/p^2*p^4=(5*m+6)*p^2 := by field_simp [p₀]
  rw [rhs]
  have p2 : p ≤ p^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) pp.le]
  have mm : 0 ≤ m*(p^2-p) := mul_nonneg hm (sub_nonneg.mpr p2)
  have mm' : m*(p^2-p) ≤ m*p^2 := by
    exact mul_le_mul_of_nonneg_left (sub_le_self _ pp.le) hm
  have z : 0 ≤ p+(p-1)*χ ∧ p+(p-1)*χ ≤ 2*p := by rcases hχ with h|h <;> rw [h] <;> constructor <;> linarith
  have z2 : (p+(p-1)*χ)^2 ≤ 4*p^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr z.2) (show 0≤2*p+(p+(p-1)*χ) by linarith [z.1])]
  have mo : 0 ≤ m+1 := by linarith
  have zlo := mul_nonneg mo (sq_nonneg (p+(p-1)*χ))
  have zhi := mul_le_mul_of_nonneg_left z2 mo
  apply abs_le.mpr
  rcases hχ with h|h <;> rw [h] at zlo zhi ⊢ <;> constructor <;> nlinarith [sq_nonneg p]

/-- Direct receiver: the bound applies to the literal fraction of bad
classes in K⁴. For K=ZMod p, χ is the ordinary mod-4 character by the
standard finite-field evaluation of the quadratic character at −1. -/
theorem actual_density {ι : Type*} [Fintype ι] [DecidableEq ι] (mix : ι → K × K)
    (hp : ringChar K≠2) (h2 : (2:K)≠0)
    (both : ∀ i, (mix i).1≠0 ∧ (mix i).2≠0)
    (indep : ∀ i j, i≠j →
      (coefficients mix i).1*(coefficients mix j).2 -
      (coefficients mix j).1*(coefficients mix i).2≠0) :
    let p : ℝ := Fintype.card K
    let m : ℝ := Fintype.card ι
    let c : ℝ := χ K
    let g : ℝ := ((badResidues mix).card:ℝ)/p^4
    |g-(m+2+2*c)/p| ≤ (5*m+6)/p^2 := by
  dsimp only
  apply density_error
  · exact_mod_cast (Fintype.card_pos : 1≤Fintype.card K)
  · positivity
  · rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:K)≠0)) with hl|hr
    · left
      have e : (χ K:ℝ)=((1:ℤ):ℝ) := congrArg (fun a : ℤ => (a:ℝ)) (show χ K=1 from hl)
      exact e.trans (by norm_num)
    · right
      have e : (χ K:ℝ)=((-1:ℤ):ℝ) := congrArg (fun a : ℤ => (a:ℝ)) (show χ K= -1 from hr)
      exact e.trans (by norm_num)
  · congr 1
    have H := bad_count mix hp h2 both indep
    unfold zeroSize mixedSize at H
    exact_mod_cast H

end LinearA4EulerDensity318
