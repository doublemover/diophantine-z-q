module
public import ValuationLucasOrientation318
public section
namespace SelectedContact318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay RawDetector318 RawWeights318
open SourceContact318 SourcePadic318 ConcretePadic318 FiniteContact318 CompressedOrientation318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact literal rational norm represented by the first detector leaf. -/
theorem norm_leaf (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    leaf0 S w=pair ((w 33)^2-2*(w 34)^2) 0 := by
  have h38 : r38 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=38)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hn : (w 37)^2=(w 33)^2-2*(w 34)^2 := by
    dsimp only [r38] at h38; linear_combination h38
  rw [leaf0_square S w source]
  ext <;> norm_num [test0,pair,pow_two]
  nlinarith [hn]

variable (p : ℕ) [Fact p.Prime]

theorem choose_H (rho : ℚ_[p]) (hr : rho^2=2) (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w) (hgood : ¬p∣contactModulus)
    (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hor : 0<place p rho hr (fH w) ∨ 0<place p rho hr (fV w))
    (hb2 : 0<place p rho hr (leaf2 S w)) (hb3 : 0<place p rho hr (leaf3 S w))
    (hb4 : 0<place p rho hr (leaf4 S w)) (hb15 : 0<place p rho hr (leaf15 S w)) :
    0<place p rho hr (fH w) := by
  have h2 := place_nat_unit p rho hr 2 (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
  have h3 := place_nat_unit p rho hr 3 (not_dvd_supported p hgood 3 (by norm_num [contactModulus]))
  have h7 := place_nat_unit p rho hr 7 (not_dvd_supported p hgood 7 (by norm_num [contactModulus]))
  have h17 := place_nat_unit p rho hr 17 hp17
  have h41 := place_nat_unit p rho hr 41 hp41
  have hk := (good_constants (place p rho hr) h2 h41).1
  have hm := ValuationLucasOrientation318.good_m_unit (place p rho hr) h2 h3 h7 h17 h41
  have hD := (discriminant_units (place p rho hr) h2 h3 h7).2
  exact ValuationLucasOrientation318.source_selects_H S w source _ hk hm hD h2 hor hb2 hb3 hb4 hb15

theorem selected_depth (rho : ℚ_[p]) (hr : rho^2=2) (S : ℚ) (w : Assignment)
    (source : Constraints (stage0 S) w)
    (hother : place p (-rho) (negative_root p rho hr) (fH w)=0)
    (h0 : (8:WithTop ℤ)≤place p rho hr (leaf0 S w)) :
    (8:WithTop ℤ)≤place p rho hr (fH w) := by
  have hn := norm_valuation p rho hr (w 33) (w 34)
  change place p rho hr (fH w)+place p (-rho) (negative_root p rho hr) (fH w)=_ at hn
  rw [hother,add_zero] at hn
  rw [norm_leaf S w source,place_rational,←hn] at h0
  exact h0

theorem bounds0_membership (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈inputs0 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    (8:WithTop ℤ)≤v (leaf0 S w) ∧ 0<v (leaf2 S w) ∧ 0<v (leaf3 S w) ∧
      0<v (leaf4 S w) ∧ 0<v (leaf15 S w) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa using hb (q0_4 S w,leaf0 S w,4) (by simp [inputs0])
  · have hh := hb (q0_1 S w,leaf2 S w,1) (by simp [inputs0])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q0_1 S w,leaf3 S w,1) (by simp [inputs0])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q0_1 S w,leaf4 S w,1) (by simp [inputs0])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q0_13 S w,leaf15 S w,13) (by simp [inputs0])
    exact lt_of_lt_of_le (by norm_num) hh

/-- Complete actual split-place detector soundness: one common selected
place satisfies every literal leaf bound and H has reciprocal-abscissa depth
at least8 there. The opposite H value is a unit. No logarithm or group-label
hypothesis occurs in this theorem. -/
theorem source_contact0_selected (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A0 S w)=a)
    (hf : rationalPlace p (t0 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨hR,hb⟩ := FiniteContact318.source_contact0 p S w source rho hr a f j hgood hp17 hA hf hpos hodd
  have hor := source_contact0_opposite p rho hr S w source a f j hgood hp17 hp41 hA hf hpos hodd
  have hleft : 0<place p rho hr (fH w) ∨ 0<place p rho hr (fV w) := by
    rcases hor with hh|hh
    · exact Or.inl hh.1
    · exact Or.inr hh.2.2.1
  have hright : 0<place p (-rho) (negative_root p rho hr) (fH w) ∨
      0<place p (-rho) (negative_root p rho hr) (fV w) := by
    rcases hor with hh|hh
    · exact Or.inr hh.2.2.2
    · exact Or.inl hh.2.1
  refine ⟨hR,?_⟩
  rcases hb with hb|hb
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds0_membership (place p rho hr) S w hb
    have hs := choose_H p rho hr S w source hgood hp17 hp41 hleft h2 h3 h4 h15
    have ho : place p (-rho) (negative_root p rho hr) (fH w)=0 := by
      rcases hor with hh|hh
      · exact hh.2.1
      · rw [hh.1] at hs; exact False.elim (lt_irrefl _ hs)
    exact Or.inl ⟨selected_depth p rho hr S w source ho h0,ho,hb⟩
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds0_membership (place p (-rho) (negative_root p rho hr)) S w hb
    have hs := choose_H p (-rho) (negative_root p rho hr) S w source hgood hp17 hp41 hright h2 h3 h4 h15
    have ho : place p rho hr (fH w)=0 := by
      rcases hor with hh|hh
      · rw [hh.2.1] at hs; exact False.elim (lt_irrefl _ hs)
      · exact hh.1
    exact Or.inr ⟨selected_depth p (-rho) (negative_root p rho hr) S w source (by simpa only [neg_neg] using ho) h0,ho,hb⟩

theorem bounds1_membership (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈inputs1 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    (8:WithTop ℤ)≤v (leaf0 S w) ∧ 0<v (leaf2 S w) ∧ 0<v (leaf3 S w) ∧
      0<v (leaf4 S w) ∧ 0<v (leaf15 S w) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa using hb (q1_4 S w,leaf0 S w,4) (by simp [inputs1])
  · have hh := hb (q1_1 S w,leaf2 S w,1) (by simp [inputs1])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q1_1 S w,leaf3 S w,1) (by simp [inputs1])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q1_1 S w,leaf4 S w,1) (by simp [inputs1])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q1_13 S w,leaf15 S w,13) (by simp [inputs1])
    exact lt_of_lt_of_le (by norm_num) hh

/-- Complete actual split-place detector soundness: one common selected
place satisfies every literal leaf bound and H has reciprocal-abscissa depth
at least8 there. The opposite H value is a unit. No logarithm or group-label
hypothesis occurs in this theorem. -/
theorem source_contact1_selected (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A1 S w)=a)
    (hf : rationalPlace p (t1 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨hR,hb⟩ := FiniteContact318.source_contact1 p S w source rho hr a f j hgood hp17 hA hf hpos hodd
  have hor := source_contact1_opposite p rho hr S w source a f j hgood hp17 hp41 hA hf hpos hodd
  have hleft : 0<place p rho hr (fH w) ∨ 0<place p rho hr (fV w) := by
    rcases hor with hh|hh
    · exact Or.inl hh.1
    · exact Or.inr hh.2.2.1
  have hright : 0<place p (-rho) (negative_root p rho hr) (fH w) ∨
      0<place p (-rho) (negative_root p rho hr) (fV w) := by
    rcases hor with hh|hh
    · exact Or.inr hh.2.2.2
    · exact Or.inl hh.2.1
  refine ⟨hR,?_⟩
  rcases hb with hb|hb
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds1_membership (place p rho hr) S w hb
    have hs := choose_H p rho hr S w source hgood hp17 hp41 hleft h2 h3 h4 h15
    have ho : place p (-rho) (negative_root p rho hr) (fH w)=0 := by
      rcases hor with hh|hh
      · exact hh.2.1
      · rw [hh.1] at hs; exact False.elim (lt_irrefl _ hs)
    exact Or.inl ⟨selected_depth p rho hr S w source ho h0,ho,hb⟩
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds1_membership (place p (-rho) (negative_root p rho hr)) S w hb
    have hs := choose_H p (-rho) (negative_root p rho hr) S w source hgood hp17 hp41 hright h2 h3 h4 h15
    have ho : place p rho hr (fH w)=0 := by
      rcases hor with hh|hh
      · rw [hh.2.1] at hs; exact False.elim (lt_irrefl _ hs)
      · exact hh.1
    exact Or.inr ⟨selected_depth p (-rho) (negative_root p rho hr) S w source (by simpa only [neg_neg] using ho) h0,ho,hb⟩

theorem bounds2_membership (v : AddValuation K (WithTop ℤ)) (S : ℚ) (w : Assignment)
    (hb : ∀x∈inputs2 S w,(2*x.2.2:ℤ)≤v x.2.1) :
    (8:WithTop ℤ)≤v (leaf0 S w) ∧ 0<v (leaf2 S w) ∧ 0<v (leaf3 S w) ∧
      0<v (leaf4 S w) ∧ 0<v (leaf15 S w) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa using hb (q2_4 S w,leaf0 S w,4) (by simp [inputs2])
  · have hh := hb (q2_1 S w,leaf2 S w,1) (by simp [inputs2])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q2_1 S w,leaf3 S w,1) (by simp [inputs2])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q2_1 S w,leaf4 S w,1) (by simp [inputs2])
    exact lt_of_lt_of_le (by norm_num) hh
  · have hh := hb (q2_13 S w,leaf15 S w,13) (by simp [inputs2])
    exact lt_of_lt_of_le (by norm_num) hh

/-- Complete actual split-place detector soundness: one common selected
place satisfies every literal leaf bound and H has reciprocal-abscissa depth
at least8 there. The opposite H value is a unit. No logarithm or group-label
hypothesis occurs in this theorem. -/
theorem source_contact2_selected (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A2 S w)=a)
    (hf : rationalPlace p (t2 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨hR,hb⟩ := FiniteContact318.source_contact2 p S w source rho hr a f j hgood hp17 hA hf hpos hodd
  have hor := source_contact2_opposite p rho hr S w source a f j hgood hp17 hp41 hA hf hpos hodd
  have hleft : 0<place p rho hr (fH w) ∨ 0<place p rho hr (fV w) := by
    rcases hor with hh|hh
    · exact Or.inl hh.1
    · exact Or.inr hh.2.2.1
  have hright : 0<place p (-rho) (negative_root p rho hr) (fH w) ∨
      0<place p (-rho) (negative_root p rho hr) (fV w) := by
    rcases hor with hh|hh
    · exact Or.inr hh.2.2.2
    · exact Or.inl hh.2.1
  refine ⟨hR,?_⟩
  rcases hb with hb|hb
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds2_membership (place p rho hr) S w hb
    have hs := choose_H p rho hr S w source hgood hp17 hp41 hleft h2 h3 h4 h15
    have ho : place p (-rho) (negative_root p rho hr) (fH w)=0 := by
      rcases hor with hh|hh
      · exact hh.2.1
      · rw [hh.1] at hs; exact False.elim (lt_irrefl _ hs)
    exact Or.inl ⟨selected_depth p rho hr S w source ho h0,ho,hb⟩
  · obtain ⟨h0,h2,h3,h4,h15⟩ := bounds2_membership (place p (-rho) (negative_root p rho hr)) S w hb
    have hs := choose_H p (-rho) (negative_root p rho hr) S w source hgood hp17 hp41 hright h2 h3 h4 h15
    have ho : place p rho hr (fH w)=0 := by
      rcases hor with hh|hh
      · rw [hh.2.1] at hs; exact False.elim (lt_irrefl _ hs)
      · exact hh.1
    exact Or.inr ⟨selected_depth p (-rho) (negative_root p rho hr) S w source (by simpa only [neg_neg] using ho) h0,ho,hb⟩

end SelectedContact318
