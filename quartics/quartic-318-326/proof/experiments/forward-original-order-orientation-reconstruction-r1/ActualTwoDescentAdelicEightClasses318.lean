module
public import ActualTwoDescentAdelicBadPlaceImages318
public section
noncomputable section
namespace ActualTwoDescentAdelicEightClasses318
set_option maxHeartbeats 16000000

open ActualTwoDescentAdelicPairData318 ActualTwoDescentAdelicNormalization318
open ActualTwoDescentAdelicBadPlaceImages318 ActualTwoDescentSignedAllBadNormalization318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentSignedComparisons318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentSignedRepresentativeTransport318
open ActualTwoDescentLiteralEightClasses318 ActualTwoDescentPrimeMonomials318
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The exact eight-class bound now applies to actual ADELIC classes, not only
classes already supplied by rational elliptic points. -/
theorem actual_adelic_eight_classes (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (A B : ℚ) (H : AdelicPair (∏ i, p i) A B) :
    ∃ ε c e : ZMod 2, ∃ r s : ℚ, r ≠ 0 ∧ s ≠ 0 ∧
      A=(3 : ℚ)^ε.val*((∏ i, p i : ℕ) : ℚ)^c.val*(monomial p beta : ℚ)^e.val*r^2 ∧
      B=(-((∏ i, p i : ℕ) : ℚ))^ε.val*s^2 := by
  obtain ⟨ε,δ,u,v,r,s,hr,hs,hA,hB⟩ := actual_adelic_normalization p hd hp3 C.residue A B H
  have Hbad := actual_adelic_all_bad_images p A B H ε δ u v r s hr hs hA hB
  have Hp := (actual_signed_all_bad_normalization p ε δ u v).mp Hbad
  obtain ⟨hδ,hv,c,e,hu⟩ := actual_represented_class_bound p hd hp2 hp3 a beta N C
    (δ+ε) u (toggle ε v) Hp.1
  have hdε : δ=ε := by linear_combination hδ
  have hvε : v=ε • ones (Option U) := by
    funext i
    have h := congrFun hv i
    change v i+ε*1=0 at h
    change v i=ε*1
    linear_combination h
  obtain ⟨t,ht,he⟩ := actual_four_monomial_classes p beta c e
  refine ⟨ε,c,e,t*r,s,mul_ne_zero ht hr,hs,?_,?_⟩
  · rw [hA,hdε,hu,firstRepresentative,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,he,mul_pow]
    ring
  · rw [hB,hvε,actual_second_torsion_representative]

end ActualTwoDescentAdelicEightClasses318
