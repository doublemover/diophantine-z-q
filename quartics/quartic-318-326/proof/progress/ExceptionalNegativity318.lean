module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public section
noncomputable section
namespace ExceptionalNegativity318
open Matrix
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

/-- Disjoint effective vectors have nonnegative cross-intersection when
all intersections between distinct components are nonnegative. -/
theorem disjoint_cross_nonneg (M:Matrix ι ι ℝ) (p n:ι→ℝ)
    (hoff:∀i j,i≠j→0≤M i j) (hp:∀i,0≤p i) (hn:∀i,0≤n i)
    (hdisj:∀i,n i*p i=0) : 0≤n ⬝ᵥ (M *ᵥ p) := by
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_nonneg
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_nonneg
  intro j _
  by_cases hij:i=j
  · subst j
    have he:n i*(M i i*p i)=M i i*(n i*p i) := by ring
    rw [he,hdisj]
    simp
  · exact mul_nonneg (hn i) (mul_nonneg (hoff i j hij) (hp j))

/-- A negative-definite real intersection matrix has strictly negative
self-intersection for every nonzero real coefficient vector. -/
theorem negative_self_intersection (M:Matrix ι ι ℝ) (hM:(-M).PosDef)
    (n:ι→ℝ) (hn:n≠0) : n ⬝ᵥ (M *ᵥ n)<0 := by
  have h:=hM.dotProduct_mulVec_pos hn
  simpa only [star_trivial,Matrix.neg_mulVec,dotProduct_neg,neg_pos] using h

/-- The exceptional negativity principle at the exact matrix level. It
uses the actual negative-definite quadratic form, not an inverse-sign premise. -/
theorem effective_of_matrix_nonpos (M:Matrix ι ι ℝ) (hM:(-M).PosDef)
    (hoff:∀i j,i≠j→0≤M i j) (z:ι→ℝ) (hz:∀i,(M *ᵥ z) i≤0) :
    ∀i,0≤z i := by
  let p:ι→ℝ:=fun i=>max (z i) 0
  let n:ι→ℝ:=fun i=>max (-z i) 0
  have hp:∀i,0≤p i:=fun i=>le_max_right _ _
  have hn:∀i,0≤n i:=fun i=>le_max_right _ _
  have hdisj:∀i,n i*p i=0 := by
    intro i
    by_cases hi:0≤z i
    · dsimp [n,p]
      rw [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi)]
      simp
    · have hi':z i≤0:=le_of_not_ge hi
      dsimp [n,p]
      rw [max_eq_right hi']
      simp
  have hdecomp:z=p-n := by
    funext i
    change z i=max (z i) 0-max (-z i) 0
    by_cases hi:0≤z i
    · rw [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi),sub_zero]
    · have hi':z i≤0:=le_of_not_ge hi
      rw [max_eq_right hi',max_eq_left (neg_nonneg.mpr hi')]
      ring
  have hcross:=disjoint_cross_nonneg M p n hoff hp hn hdisj
  have hpair: n ⬝ᵥ (M *ᵥ z)≤0 := by
    unfold dotProduct
    exact Finset.sum_nonpos (fun i _=>mul_nonpos_of_nonneg_of_nonpos (hn i) (hz i))
  rw [hdecomp,Matrix.mulVec_sub,dotProduct_sub] at hpair
  have hnzero:n=0 := by
    by_contra hne
    have hneg:=negative_self_intersection M hM n hne
    linarith only [hcross,hpair,hneg]
  intro i
  have hi:=congrFun hnzero i
  have hbound : -z i≤n i := le_max_left _ _
  simp only [Pi.zero_apply] at hi
  linarith only [hi,hbound]

/-- Nonexceptional effective components contribute nonnegative intersections
and can be retained explicitly without weakening the negativity argument. -/
theorem effective_of_intersections_nonpos (M:Matrix ι ι ℝ) (hM:(-M).PosDef)
    (hoff:∀i j,i≠j→0≤M i j) (z e:ι→ℝ) (he:∀i,0≤e i)
    (hz:∀i,(M *ᵥ z) i+e i≤0) : ∀i,0≤z i := by
  apply effective_of_matrix_nonpos M hM hoff z
  intro i
  linarith only [he i,hz i]

/-- Exact coefficientwise form used for Z=pullback(D)-K: effectiveness off
the exceptional locus and nonpositive exceptional intersections force
coefficientwise canonical-divisor domination on the exceptional locus too. -/
theorem canonical_coefficients_le (M:Matrix ι ι ℝ) (hM:(-M).PosDef)
    (hoff:∀i j,i≠j→0≤M i j) (D K e:ι→ℝ) (he:∀i,0≤e i)
    (hz:∀i,(M *ᵥ (D-K)) i+e i≤0) : ∀i,K i≤D i := by
  have h:=effective_of_intersections_nonpos M hM hoff (D-K) e he hz
  intro i
  have hi:=h i
  change 0≤D i-K i at hi
  linarith only [hi]

/-- A finite family of nonexceptional effective components gives the required
nonnegative outside contribution by its actual intersection matrix. -/
theorem canonical_domination_with_outside {κ:Type*} [Fintype κ]
    (M:Matrix ι ι ℝ) (hM:(-M).PosDef) (hoff:∀i j,i≠j→0≤M i j)
    (C:Matrix ι κ ℝ) (hC:∀i j,0≤C i j) (b:κ→ℝ) (hb:∀j,0≤b j)
    (D K:ι→ℝ) (hz:∀i,(M *ᵥ (D-K)) i+(C *ᵥ b) i≤0) :
    ∀i,K i≤D i := by
  apply canonical_coefficients_le M hM hoff D K (C *ᵥ b) _ hz
  intro i
  simp only [Matrix.mulVec,dotProduct]
  exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC i j) (hb j))

end ExceptionalNegativity318
