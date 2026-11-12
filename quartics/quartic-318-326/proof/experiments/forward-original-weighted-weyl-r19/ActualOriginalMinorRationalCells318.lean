module
public import ActualOriginalMinorDirichlet318
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public section
noncomputable section
namespace ActualOriginalMinorRationalCells318
open ActualOriginalMajorArcDomain318 ActualOriginalReducedArcIndex318
open ActualOriginalMinorDirichlet318 MeasureTheory
open scoped BigOperators

@[expose] def dirichletWidth (Q : ℕ) (q : ℤ) : ℝ := 1/(((Q : ℝ)+1)*(q : ℝ))
@[expose] def minorCell (N Q : ℕ) (B : ℝ) (a q : ℤ) : Set ℝ :=
  minorDomain N B ∩ Set.Icc ((a : ℝ)/(q : ℝ)-dirichletWidth Q q)
    ((a : ℝ)/(q : ℝ)+dirichletWidth Q q)
@[expose] def rationalIndices (N Q : ℕ) : Finset (ℤ×ℤ) :=
  ((Finset.Icc ((N : ℤ)+1) Q) ×ˢ (Finset.Icc (1 : ℤ) Q)).filter
    (fun i => i.2<i.1 ∧ IsCoprime i.1 i.2)

lemma actual_minor_interior (N : ℕ) (hN : 0<N) (B t : ℝ)
    (ht : t∈minorDomain N B) : radius N B<t ∧ t≤1-radius N B := by
  refine ⟨?_,ht.1.2⟩
  by_contra hh
  obtain ⟨i,hi⟩ := actual_reduced_arc_index N 0 1 (by omega)
    (by exact_mod_cast hN) (by omega) (by omega) isCoprime_one_left
  have hi0 : center i=0 := by simpa using hi
  apply ht.2
  apply Set.mem_iUnion.mpr
  refine ⟨i,?_⟩
  change center i-radius N B<t ∧ t≤center i+radius N B
  rw [hi0]
  constructor
  · simpa using ht.1.1
  · simpa using le_of_not_gt hh

lemma actual_minor_cell_measurable (N Q : ℕ) (B : ℝ) (a q : ℤ) :
    MeasurableSet (minorCell N Q B a q) :=
  (minor_measurable N B).inter measurableSet_Icc

lemma actual_minor_cell_measure (N Q : ℕ) (B : ℝ) (a q : ℤ) (hq : 0<q) :
    volume.real (minorCell N Q B a q)≤2*dirichletWidth Q q := by
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hw : 0≤dirichletWidth Q q := by unfold dirichletWidth; positivity
  have hm := measureReal_mono (μ:=volume)
    (show minorCell N Q B a q⊆Set.Icc ((a : ℝ)/(q : ℝ)-dirichletWidth Q q)
      ((a : ℝ)/(q : ℝ)+dirichletWidth Q q) from Set.inter_subset_right)
    (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  rw [Real.volume_real_Icc_of_le (by linarith)] at hm
  linarith

/-- A finite cover of the literal minor domain by reduced canonical
fractions with N<q<=Q and 1<=a<q. The modulus-one arc removes both possible
endpoint/wrap artefacts. Cells may overlap; no disjointness is claimed. -/
theorem actual_minor_rational_cover (N : ℕ) (hN : 0<N) (B : ℝ)
    (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (Q : ℕ) (hQ : 0<Q) (hwidth : 1/((Q : ℝ)+1)<radius N B) :
    minorDomain N B⊆⋃ i∈rationalIndices N Q, minorCell N Q B i.2 i.1 := by
  intro t ht
  obtain ⟨a,q,hNq,hqQ,hc,he,he'⟩ := actual_minor_dirichlet N hN B hB hs Q hQ hwidth t ht
  have hq : 0<q := by omega
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast (show 1≤q by omega)
  have hQp : (0 : ℝ)<(Q : ℝ)+1 := by positivity
  have he0 : |t-(a : ℝ)/(q : ℝ)|<radius N B := by
    apply lt_of_le_of_lt (he.trans _) hwidth
    apply one_div_le_one_div_of_le hQp
    nlinarith
  have ht' := actual_minor_interior N hN B t ht
  have hb := abs_lt.mp he0
  have har : (0 : ℝ)<(a : ℝ)/(q : ℝ) := by linarith
  have haqR : (a : ℝ)/(q : ℝ)<1 := by linarith
  have ha : 0<a := by exact_mod_cast (pos_of_div_pos_left har hqr.le)
  have haq : a<q := by exact_mod_cast (div_lt_one hqr).mp haqR
  have hi : (q,a)∈rationalIndices N Q := by
    simp only [rationalIndices,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
    exact ⟨⟨⟨by omega,hqQ⟩,⟨by omega,by omega⟩⟩,haq,hc⟩
  apply Set.mem_iUnion.mpr
  refine ⟨(q,a),Set.mem_iUnion.mpr ⟨hi,ht,?_⟩⟩
  have hh := abs_le.mp he
  change (a : ℝ)/(q : ℝ)-dirichletWidth Q q≤t ∧
    t≤(a : ℝ)/(q : ℝ)+dirichletWidth Q q
  dsimp [dirichletWidth]
  constructor <;> linarith

end ActualOriginalMinorRationalCells318
