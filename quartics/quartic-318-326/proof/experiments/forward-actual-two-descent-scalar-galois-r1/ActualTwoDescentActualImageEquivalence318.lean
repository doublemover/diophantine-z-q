module
public import ActualTwoDescentThreeUnitPoints318
public section
noncomputable section
namespace ActualTwoDescentActualImageEquivalence318
open ActualTwoDescentActualLocalClassBound318 ActualTwoDescentThreeUnitPoints318
open ActualTwoDescentRepresentedThree318 ActualTwoDescentBetaSupportPoints318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentLocalClassification318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Every actual matrix-kernel monomial has GENUINE local curve witnesses
at all support primes and3. This constructs the local inputs rather than
postulating a converse to the necessary signature comparison. -/
theorem actual_kernel_locally_represented (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ j, p j : ℕ) : ZMod 12)=11)
    (u : Option U → ZMod 2) (hK : laplacian p *ᵥ u=0) :
    BadLocallyRepresented p 0 u 0 := by
  have hn3 : ((∏ j, p j : ℕ) : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
    simpa using h
  have hs := actual_beta_support_points p hd hp2 u hK
  have h3 := actual_three_unit_point (monomial p u) (∏ j, p j)
    (actual_monomial_coprime_three p hp3 u) hn3
  constructor
  · intro i
    simpa only [firstRepresentative,ZMod.val_zero,pow_zero,one_mul,
      monomial,Pi.zero_apply,Finset.prod_const_one] using
      actual_local_kummer_represented _ _ (hs i)
  · simpa only [firstRepresentative,ZMod.val_zero,pow_zero,one_mul,
      monomial,Pi.zero_apply,Finset.prod_const_one] using actual_local_kummer_represented _ _ h3

/-- Exact equivalence between the positive formal comparison space and
the intersection of the ACTUAL local Kummer images at the treated bad
places. Full Selmer identification additionally requires good places,
normalization of arbitrary classes and the global elliptic framework. -/
theorem actual_bad_local_image_equivalence (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (δ : ZMod 2) (u v : Option U → ZMod 2) :
    BadLocallyRepresented p δ u v ↔ Admissible p δ u v := by
  constructor
  · exact actual_local_representation_admissible p hd hp2 hp3 C.residue δ u v
  · intro H
    obtain ⟨rfl,rfl,c,e,rfl⟩ := (actual_local_classification p hp2 hp3 a beta N C δ u v).mp H
    apply actual_kernel_locally_represented p hd hp2 hp3 C.residue
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,
      actual_laplacian_ones,C.beta_kernel,smul_zero,smul_zero,add_zero]

end ActualTwoDescentActualImageEquivalence318
