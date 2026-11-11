module
public import ActualTwoDescentOldCorePreservation318
public section
noncomputable section
namespace ActualTwoDescentSimultaneousCoreChoice318
open ActualTwoDescentThetaDiagonal318 ActualTwoDescentQ0PrimeReplacement318
open ActualTwoDescentQ0CoreReplacement318 ActualTwoDescentOldCorePreservation318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentMatrixCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- The diagonal choice is realized by a NEW ACTUAL q0 prime. The old
core is identical, while the enlarged actual core becomes nonsingular.
Thus the two unit-core results concern the same final support and primes. -/
theorem actual_simultaneous_core_choice {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J]
    (p : Option (U ⊕ J) → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hc : ∀ i, Nat.Coprime (p i) 12) (htype : (p none : ZMod 12)=7)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (a : Option (U ⊕ J) → ZMod 2)
    (hsmall : IsUnit (fun i j => sharp p a (some (Sum.inl i)) (some (Sum.inl j)) :
      Matrix U U (ZMod 2))) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ p' : Option (U ⊕ J) → ℕ,
      (∀ i, (p' i).Prime) ∧ Function.Injective p' ∧
      (∀ i, p' (some i)=p (some i)) ∧
      N < p' none ∧ p' none ∉ forbidden ∧ p' none ≠ p none ∧
      (p' none : ZMod 12)=7 ∧ ((∏ i, p' i : ℕ) : ZMod 12)=11 ∧
      IsUnit (fun i j => sharp p' a (some i) (some j) : Matrix (U ⊕ J) (U ⊕ J) (ZMod 2)) ∧
      (∀ i j : U, sharp p' a (some (Sum.inl i)) (some (Sum.inl j))=
        sharp p a (some (Sum.inl i)) (some (Sum.inl j))) ∧
      (∀ i : U, edges p' (some (Sum.inl i)) none=edges p (some (Sum.inl i)) none) := by
  let M : Matrix (U ⊕ J) (U ⊕ J) (ZMod 2) := fun i j => sharp p a (some i) (some j)
  obtain ⟨t,ht⟩ := actual_theta_diagonal M hsmall
  obtain ⟨p',hp',hd',hfix,hlarge,havoid,hnew,htype',hn',hbits⟩ :=
    actual_q0_prime_replacement p hd hc htype hn (Sum.elim (fun _ : U => 0) t) forbidden N
  have he := actual_sharp_core_replacement p p' hfix a (Sum.elim (fun _ : U => 0) t) hbits
  refine ⟨p',hp',hd',hfix,hlarge,havoid,hnew,htype',hn',?_,?_,?_⟩
  · rw [he]
    exact ht
  · intro i j
    have h := congrFun (congrFun he (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.diagonal_apply] using h
  · intro i
    simpa only [Sum.elim_inl,add_zero] using hbits (Sum.inl i)

end ActualTwoDescentSimultaneousCoreChoice318
