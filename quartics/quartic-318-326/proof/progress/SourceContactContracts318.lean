module
public import SourceContactDivisibility318
public import ConsumedContactHeight318
public section
namespace SourceContactContracts318
open CircuitReplay Raw318FinalReplay RawWeights318
open ConcretePadic318 FiniteContact318 SourceLabelData318 SourceContactDivisibility318
open ConsumedContactHeight318 ContactPrimeLimits318 ContactRadical318
set_option maxHeartbeats 0
noncomputable section

theorem polynomial_ne_zero (A t e:ℚ) (hA:A≠0)
    (he:e*contactPolynomial t=(A*(t-1))^5) : contactPolynomial t≠0 := by
  intro hz
  rw [hz,mul_zero] at he
  have hd:A*(t-1)=0:=(pow_eq_zero_iff (by decide:5≠0)).mp he.symm
  have ht:t=1:=sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hA)
  norm_num [ht,contactPolynomial] at hz

theorem source_polynomial0_ne (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    contactPolynomial (t0 S w)≠0 := by
  apply polynomial_ne_zero (A0 S w) (t0 S w) (e0 S w)
    (FiniteScale318.A0_ne_zero S w)
  simpa only [F0_actual S w source,delta0] using eF0_source S w source

/-- Full bad-prime source contract, with the coherent labels fixed once. -/
theorem source_contact0_contracts
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source) :
    ContactDivisibility (t0 ((3:ℚ)^65536) w) (highTarget labels) 13 ∧
    ContactDivisibility (t0 ((3:ℚ)^65536) w) (lowTarget w labels).num 4 := by
  have hh:∀(p:ℕ)(hp:p.Prime),p∉badPrimes→∀(j:Fin 5)(f:ℤ),
      @rationalPlace p ⟨hp⟩ (t0 ((3:ℚ)^65536) w-root j)=f→0<f→Odd f→
      (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
    intro p hp hg j f hf hpos hodd
    letI:Fact p.Prime:=⟨hp⟩
    obtain ⟨h19,hgood,h17,h41⟩:=good_exclusions p hp hg
    exact source_contact0_divisibility p h19 w source labels f j hgood h17 h41 hf hpos hodd
  exact ⟨fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).1,
    fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).2⟩

/-- Conditional only on the explicitly upstream geometric five-contact
height theorem and nonvanishing of the selected integer target. All local
source arithmetic and rational contact contracts are proved. -/
theorem source_high_height0 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:highTarget labels≠0) :
    NumberField.absLogHeight₁ (t0 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|(highTarget labels:ℝ)|^((49:ℝ)/104) :=
  detector_high13 hFive _ (source_polynomial0_ne _ w source) _ hN
    (source_contact0_contracts w source labels).1

theorem source_low_height0 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:(lowTarget w labels).num≠0) :
    NumberField.absLogHeight₁ (t0 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|((lowTarget w labels).num:ℝ)|^((49:ℝ)/32) :=
  detector_low4 hFive _ (source_polynomial0_ne _ w source) _ hN
    (source_contact0_contracts w source labels).2

theorem source_polynomial1_ne (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    contactPolynomial (t1 S w)≠0 := by
  apply polynomial_ne_zero (A1 S w) (t1 S w) (e1 S w)
    (FiniteScale318.A1_ne_zero S w source)
  simpa only [F1_actual S w source,delta1] using eF1_source S w source

/-- Full bad-prime source contract, with the coherent labels fixed once. -/
theorem source_contact1_contracts
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source) :
    ContactDivisibility (t1 ((3:ℚ)^65536) w) (highTarget labels) 13 ∧
    ContactDivisibility (t1 ((3:ℚ)^65536) w) (lowTarget w labels).num 4 := by
  have hh:∀(p:ℕ)(hp:p.Prime),p∉badPrimes→∀(j:Fin 5)(f:ℤ),
      @rationalPlace p ⟨hp⟩ (t1 ((3:ℚ)^65536) w-root j)=f→0<f→Odd f→
      (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
    intro p hp hg j f hf hpos hodd
    letI:Fact p.Prime:=⟨hp⟩
    obtain ⟨h19,hgood,h17,h41⟩:=good_exclusions p hp hg
    exact source_contact1_divisibility p h19 w source labels f j hgood h17 h41 hf hpos hodd
  exact ⟨fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).1,
    fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).2⟩

/-- Conditional only on the explicitly upstream geometric five-contact
height theorem and nonvanishing of the selected integer target. All local
source arithmetic and rational contact contracts are proved. -/
theorem source_high_height1 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:highTarget labels≠0) :
    NumberField.absLogHeight₁ (t1 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|(highTarget labels:ℝ)|^((49:ℝ)/104) :=
  detector_high13 hFive _ (source_polynomial1_ne _ w source) _ hN
    (source_contact1_contracts w source labels).1

theorem source_low_height1 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:(lowTarget w labels).num≠0) :
    NumberField.absLogHeight₁ (t1 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|((lowTarget w labels).num:ℝ)|^((49:ℝ)/32) :=
  detector_low4 hFive _ (source_polynomial1_ne _ w source) _ hN
    (source_contact1_contracts w source labels).2

theorem source_polynomial2_ne (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    contactPolynomial (t2 S w)≠0 := by
  apply polynomial_ne_zero (A2 S w) (t2 S w) (e2 S w)
    (FiniteScale318.A2_ne_zero S w source)
  simpa only [F2_actual S w source,delta2] using eF2_source S w source

/-- Full bad-prime source contract, with the coherent labels fixed once. -/
theorem source_contact2_contracts
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source) :
    ContactDivisibility (t2 ((3:ℚ)^65536) w) (highTarget labels) 13 ∧
    ContactDivisibility (t2 ((3:ℚ)^65536) w) (lowTarget w labels).num 4 := by
  have hh:∀(p:ℕ)(hp:p.Prime),p∉badPrimes→∀(j:Fin 5)(f:ℤ),
      @rationalPlace p ⟨hp⟩ (t2 ((3:ℚ)^65536) w-root j)=f→0<f→Odd f→
      (p:ℤ)^13∣highTarget labels ∧ (p:ℤ)^4∣(lowTarget w labels).num := by
    intro p hp hg j f hf hpos hodd
    letI:Fact p.Prime:=⟨hp⟩
    obtain ⟨h19,hgood,h17,h41⟩:=good_exclusions p hp hg
    exact source_contact2_divisibility p h19 w source labels f j hgood h17 h41 hf hpos hodd
  exact ⟨fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).1,
    fun p hp hg j f hf hpos hodd=>(hh p hp hg j f hf hpos hodd).2⟩

/-- Conditional only on the explicitly upstream geometric five-contact
height theorem and nonvanishing of the selected integer target. All local
source arithmetic and rational contact contracts are proved. -/
theorem source_high_height2 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:highTarget labels≠0) :
    NumberField.absLogHeight₁ (t2 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|(highTarget labels:ℝ)|^((49:ℝ)/104) :=
  detector_high13 hFive _ (source_polynomial2_ne _ w source) _ hN
    (source_contact2_contracts w source labels).1

theorem source_low_height2 (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hN:(lowTarget w labels).num≠0) :
    NumberField.absLogHeight₁ (t2 ((3:ℚ)^65536) w)≤
      (HeightSeparation318.heightConstant+Real.log 3)*|((lowTarget w labels).num:ℝ)|^((49:ℝ)/32) :=
  detector_low4 hFive _ (source_polynomial2_ne _ w source) _ hN
    (source_contact2_contracts w source labels).2

end
end SourceContactContracts318
#print axioms SourceContactContracts318.source_contact0_contracts
#print axioms SourceContactContracts318.source_high_height0
#print axioms SourceContactContracts318.source_contact1_contracts
#print axioms SourceContactContracts318.source_high_height1
#print axioms SourceContactContracts318.source_contact2_contracts
#print axioms SourceContactContracts318.source_high_height2
