module
public import ActualOriginalMinorRationalExclusion318
public section
noncomputable section
namespace ActualOriginalMinorDirichlet318
open ActualOriginalMajorArcDomain318 ActualOriginalMinorRationalExclusion318

/-- Native Dirichlet approximation is reduced before consumption. Both the
strong Q-dependent error and the q^-2 error are retained. -/
theorem actual_reduced_dirichlet (t : ℝ) (Q : ℕ) (hQ : 0<Q) :
    ∃ a q : ℤ, 0<q ∧ q≤Q ∧ IsCoprime q a ∧
      |t-(a : ℝ)/(q : ℝ)|≤1/(((Q : ℝ)+1)*(q : ℝ)) ∧
      |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 := by
  obtain ⟨r,he,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hQ
  have hp : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hdR : (r.den : ℝ)≤Q := by exact_mod_cast hd
  have hc : IsCoprime (r.den : ℤ) r.num := by
    apply IsCoprime.symm
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using r.reduced
  have hval : (r : ℝ)=(r.num : ℝ)/(r.den : ℝ) := by
    exact_mod_cast r.num_div_den.symm
  rw [hval] at he
  refine ⟨r.num,r.den,by exact_mod_cast r.pos,by exact_mod_cast hd,hc,?_,?_⟩
  · simpa only [Int.cast_natCast] using he
  · simp only [Int.cast_natCast]
    apply he.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hp)
    nlinarith

/-- Actual minor points have a genuinely produced reduced approximant
with N<q<=Q whenever the Dirichlet width is strictly below the major radius.
No irrationality assumption is used. -/
theorem actual_minor_dirichlet (N : ℕ) (hN : 0<N) (B : ℝ)
    (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (Q : ℕ) (hQ : 0<Q) (hwidth : 1/((Q : ℝ)+1)<radius N B)
    (t : ℝ) (ht : t∈minorDomain N B) :
    ∃ a q : ℤ, (N : ℤ)<q ∧ q≤Q ∧ IsCoprime q a ∧
      |t-(a : ℝ)/(q : ℝ)|≤1/(((Q : ℝ)+1)*(q : ℝ)) ∧
      |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 := by
  obtain ⟨a,q,hq,hqQ,hc,he,he'⟩ := actual_reduced_dirichlet t Q hQ
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hQp : (0 : ℝ)<(Q : ℝ)+1 := by positivity
  have he0 : |t-(a : ℝ)/(q : ℝ)|≤1/((Q : ℝ)+1) := by
    apply he.trans
    apply one_div_le_one_div_of_le hQp
    nlinarith
  have hNq : (N : ℤ)<q := by
    by_contra hh
    have hh' := actual_minor_small_denominator_error N hN B hB hs t ht a q hq (by omega) hc
    linarith
  exact ⟨a,q,hNq,hqQ,hc,he,he'⟩

/-- A concrete Dirichlet order, rather than an assumed denominator choice. -/
lemma actual_minor_dirichlet_order (N : ℕ) (hN : 0<N) (B : ℝ) (hB : 0<B) :
    0<⌈B^2/(N : ℝ)⌉₊ ∧
      1/((⌈B^2/(N : ℝ)⌉₊ : ℝ)+1)<radius N B := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hx : (0 : ℝ)<B^2/(N : ℝ) := div_pos (sq_pos_of_pos hB) hn
  have hc := Nat.le_ceil (B^2/(N : ℝ))
  have hcp : (0 : ℝ)<(⌈B^2/(N : ℝ)⌉₊ : ℝ) := hx.trans_le hc
  refine ⟨by exact_mod_cast hcp,?_⟩
  have hh : 1/((⌈B^2/(N : ℝ)⌉₊ : ℝ)+1)<1/(B^2/(N : ℝ)) :=
    one_div_lt_one_div_of_lt hx (by linarith)
  simpa only [one_div_div,radius] using hh

end ActualOriginalMinorDirichlet318
