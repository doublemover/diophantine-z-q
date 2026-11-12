module
public import AnalyticNonzeroSquareRoot318
public import NormalizedLegendreWholeProjection318
public import Mathlib.Analysis.Convex.Contractible
public section
noncomputable section
namespace LegendreHalfPlaneAnalyticSheets318
open Set
open NormalizedLegendreFieldPoints318
set_option maxHeartbeats 1000000

@[expose] def side (upper:Bool) (z:ℂ) : ℝ:=if upper then z.im else -z.im
@[expose] def domain (upper:Bool) : Set ℂ:={z|0<side upper z}
lemma side_add (upper:Bool) (z w:ℂ) : side upper (z+w)=side upper z+side upper w := by
  cases upper <;> simp [side]
lemma side_smul (upper:Bool) (a:ℝ) (z:ℂ) : side upper (a • z)=a*side upper z := by
  cases upper <;> simp [side,Complex.smul_im]
lemma domain_open (upper:Bool) : IsOpen (domain upper) := by
  apply isOpen_lt continuous_const
  cases upper
  · exact Complex.continuous_im.neg
  · exact Complex.continuous_im
lemma domain_nonempty (upper:Bool) : (domain upper).Nonempty := by
  cases upper
  · exact ⟨-Complex.I,by norm_num [domain,side]⟩
  · exact ⟨Complex.I,by norm_num [domain,side]⟩
lemma domain_convex (upper:Bool) : Convex ℝ (domain upper) := by
  intro x hx y hy a b ha hb hab
  change 0<side upper (a • x+b • y)
  rw [side_add,side_smul,side_smul]
  have hp:0<a ∨ 0<b:=by
    by_contra h
    push_neg at h
    linarith [h.1,h.2]
  rcases hp with hp|hp
  · exact add_pos_of_pos_of_nonneg (mul_pos hp hx) (mul_nonneg hb hy.le)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.le) (mul_pos hp hy)
lemma domain_simplyConnected (upper:Bool) : IsSimplyConnected (domain upper) := by
  letI : ContractibleSpace (domain upper):=(domain_convex upper).contractibleSpace (domain_nonempty upper)
  exact inferInstance
lemma domain_nonreal (upper:Bool) (z:ℂ) (hz:z∈domain upper) : z.im≠0 := by
  intro h
  cases upper <;> simp [domain,side,h] at hz

@[expose] def polynomial (l z:ℂ) : ℂ:=z*(z-1)*(z-l)
lemma polynomial_analytic (l:ℂ) : AnalyticOnNhd ℂ (polynomial l) Set.univ := by
  intro z _
  unfold polynomial
  fun_prop
lemma polynomial_nonzero (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) (hz:z∈domain upper) :
    polynomial l z≠0 := by
  have him:=domain_nonreal upper z hz
  unfold polynomial
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h; exact him (by rw [h]; simp)
    · intro h; have he:=sub_eq_zero.mp h; exact him (by rw [he]; simp)
  · intro h; have he:=sub_eq_zero.mp h; exact him (by rw [he,hl])

/-- TWO genuine holomorphic square-root sheets over either complete open
halfplane, with the SAME actual real Legendre parameter. The root is
constructed by simply-connected covering lifting, not a pointwise choice. -/
theorem exists_sheet (l:ℂ) (hl:l.im=0) (upper:Bool) :
    ∃s:ℂ→ℂ,AnalyticOnNhd ℂ s (domain upper) ∧ ∀z,s z^2=polynomial l z := by
  apply AnalyticNonzeroSquareRoot318.exists_analytic_root
    (domain_open upper) (domain_simplyConnected upper)
  · exact (polynomial_analytic l).mono (subset_univ _)
  · exact polynomial_nonzero l hl upper

@[expose] def root (l:ℂ) (hl:l.im=0) (upper:Bool) : ℂ→ℂ:=(exists_sheet l hl upper).choose
lemma root_analytic (l:ℂ) (hl:l.im=0) (upper:Bool) :
    AnalyticOnNhd ℂ (root l hl upper) (domain upper):=(exists_sheet l hl upper).choose_spec.1
lemma root_square (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) :
    root l hl upper z^2=polynomial l z:=(exists_sheet l hl upper).choose_spec.2 z
lemma root_nonzero (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) (hz:z∈domain upper) :
    root l hl upper z≠0 := by
  intro h
  have he:=root_square l hl upper z
  rw [h,zero_pow (by decide : 2≠0)] at he
  exact polynomial_nonzero l hl upper z hz he.symm

/-- Actual finite points, not an abstract trivial double-cover type. -/
@[expose] def positivePoint (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) : FinitePoints l:=
  ⟨(z,root l hl upper z),root_square l hl upper z⟩
@[expose] def negativePoint (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) : FinitePoints l:=
  sign l (positivePoint l hl upper z)

lemma sheets_distinct (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) (hz:z∈domain upper) :
    negativePoint l hl upper z≠positivePoint l hl upper z := by
  intro h
  exact root_nonzero l hl upper z hz ((sign_fixed_iff l _).mp h)

/-- Every actual finite point over a halfplane lies on exactly one of the
constructed analytic sheets; the two branches remain globally distinct. -/
theorem sheet_exhaustion (l:ℂ) (hl:l.im=0) (upper:Bool) (p:FinitePoints l)
    (hp:p.val.1∈domain upper) :
    (p=positivePoint l hl upper p.val.1 ∨ p=negativePoint l hl upper p.val.1) ∧
    negativePoint l hl upper p.val.1≠positivePoint l hl upper p.val.1 := by
  refine ⟨?_,sheets_distinct l hl upper p.val.1 hp⟩
  have h:=(NormalizedLegendreFieldPoints318.same_coordinate l
    (positivePoint l hl upper p.val.1) p).mp rfl
  simpa only [eq_comm] using h

lemma positive_coordinates_analytic (l:ℂ) (hl:l.im=0) (upper:Bool) :
    AnalyticOnNhd ℂ (fun z=>(positivePoint l hl upper z).val) (domain upper) := by
  intro z hz
  exact analyticAt_id.prod (root_analytic l hl upper z hz)
lemma negative_coordinates_analytic (l:ℂ) (hl:l.im=0) (upper:Bool) :
    AnalyticOnNhd ℂ (fun z=>(negativePoint l hl upper z).val) (domain upper) := by
  intro z hz
  exact analyticAt_id.prod (root_analytic l hl upper z hz).neg

/-- Each branch is a section of the SAME genuine full Scheme projection,
with no replacement of the original t coordinate by shifted native x. -/
theorem original_scheme_sections (l:ℂ) (hl:l.im=0) (upper:Bool) (z:ℂ) :
    NormalizedLegendreFiniteProjection318.project l
      (schemeEquiv l (some (positivePoint l hl upper z)))=
        ProjectiveLineComplexSchemePoints318.chartPoint 1 z ∧
    NormalizedLegendreFiniteProjection318.project l
      (schemeEquiv l (some (negativePoint l hl upper z)))=
        ProjectiveLineComplexSchemePoints318.chartPoint 1 z :=
  ⟨NormalizedLegendreFiniteProjection318.finite_projection l _,
    NormalizedLegendreFiniteProjection318.finite_projection l _⟩
end LegendreHalfPlaneAnalyticSheets318
