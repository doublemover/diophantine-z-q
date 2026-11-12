module
public import ActualTwoDescentAdjoinedPrimes318
public section
noncomputable section
namespace ActualTwoDescentBetaThetaFamily318
open ActualTwoDescentSmallPattern318 ActualTwoDescentSmallPrimeAssembly318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentAdjoinedPrimes318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentSymbolTable318 ActualTwoDescentAuxiliaryTypes318
open ActualTwoDescentEdgeAction318 ActualTwoDescentMutualSymbolRows318
open scoped BigOperators
set_option maxHeartbeats 16000000

def seed {d : ℕ} {J : Type*} (qB : BetaIndex d → ℕ) (qJ : J → ℕ) : BetaIndex d ⊕ J → ℕ :=
  Sum.elim qB qJ
def seedBits (d : ℕ) (J : Type*) (k : ℕ) : BetaIndex d ⊕ J → Bool :=
  Sum.elim (prescribedBits d k) (fun _ => false)
abbrev JointFamily (d : ℕ) {J : Type*} (qB : BetaIndex d → ℕ) (qJ : J → ℕ)
    (forbidden : Finset ℕ) (N : ℕ) :=
  PrimeFamily (seed qB qJ) (seedBits d J) (fun _ _ => false)
    (fun k => decide (k=d)) forbidden N (d+1)

/-- Restriction preserves every produced auxiliary value, not just its
existence. The earlier first-twist producer applies to precisely this family. -/
def betaRestriction {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N) :
    Family d qB forbidden N where
  value := F.value
  prime := F.prime
  large := F.large
  injective := F.injective
  seed_ne := fun i b => F.seed_ne i (Sum.inl b)
  avoid := F.avoid
  residue := F.residue
  coprime := F.coprime
  old_symbol := fun i b => F.old_symbol i (Sum.inl b)
  earlier_symbol := F.earlier_symbol

def fullPrimes {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N) :
    Option (CoreIndex d ⊕ J) → ℕ := adjoin (assembled (betaRestriction F)) qJ

instance seed_prime {d : ℕ} {J : Type*} (qB : BetaIndex d → ℕ) (qJ : J → ℕ)
    [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime] (i : BetaIndex d ⊕ J) :
    Fact (seed qB qJ i).Prime := ⟨by cases i <;> exact Fact.out⟩
instance full_prime {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N)
    (i : Option (CoreIndex d ⊕ J)) : Fact (fullPrimes F i).Prime := by
  change Fact (adjoin (assembled (betaRestriction F)) qJ i).Prime
  infer_instance

lemma seed_injective {d : ℕ} {J : Type*} (qB : BetaIndex d → ℕ) (qJ : J → ℕ)
    (hB : Function.Injective qB) (hJ : Function.Injective qJ)
    (hdis : ∀ b j, qB b ≠ qJ j) : Function.Injective (seed qB qJ) := by
  intro i j he
  cases i with
  | inl b =>
    cases j with
    | inl c => exact congrArg Sum.inl (hB he)
    | inr j => exact False.elim (hdis b j he)
  | inr j =>
    cases j with
    | inl b => exact False.elim (hdis b j he.symm)
    | inr k => exact congrArg Sum.inr (hJ he)

lemma full_injective {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N)
    (hB : Function.Injective qB) (hJ : Function.Injective qJ)
    (hdis : ∀ b j, qB b ≠ qJ j) : Function.Injective (fullPrimes F) := by
  apply adjoin_injective _ _ (assembled_injective (betaRestriction F) hB) hJ
  intro i j
  cases i with
  | none => exact F.seed_ne (Fin.last d) (Sum.inr j)
  | some i =>
    cases i with
    | inl b => exact hdis b j
    | inr i => exact F.seed_ne i.castSucc (Sum.inr j)

lemma full_coprime {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N)
    (hB : ∀ b, Nat.Coprime (qB b) 12) (hJ : ∀ j, Nat.Coprime (qJ j) 12) :
    ∀ i, Nat.Coprime (fullPrimes F i) 12 :=
  adjoin_coprime _ _ (assembled_coprime (betaRestriction F) hB) hJ

lemma theta_at_I_zero {d : ℕ} {J : Type*} {qB : BetaIndex d → ℕ} {qJ : J → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N) (i : Fin d) (j : J) :
    edges (fullPrimes F) (some (Sum.inr j)) (oldEmbedding (iIndex i))=0 := by
  have hs := actual_bit_of_sign _ _ _ (F.old_symbol i.castSucc (Sum.inr j))
  simpa [edges,fullPrimes,adjoin,assembled,betaRestriction,oldEmbedding,iIndex,seed,seedBits,boolBit] using hs

/-- The I/theta blocks vanish in BOTH directions at the actual primes;
the reverse direction is derived from the actual type1 parity. -/
lemma I_at_theta_zero {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    {qB : BetaIndex d → ℕ} {qJ : J → ℕ} [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N)
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hcB : ∀ b, Nat.Coprime (qB b) 12) (hcJ : ∀ j, Nat.Coprime (qJ j) 12)
    (i : Fin d) (j : J) :
    edges (fullPrimes F) (oldEmbedding (iIndex i)) (some (Sum.inr j))=0 := by
  have hd := full_injective F hB hJ hdis
  have hc := full_coprime F hcB hcJ
  have hp2 : ∀ k, fullPrimes F k ≠ 2 := by
    intro k he
    have h := hc k
    rw [he] at h
    norm_num at h
  have hs : parity (fullPrimes F) (oldEmbedding (iIndex i))=0 :=
    (actual_type_one _ (assembled_type_I (betaRestriction F) i)).1
  rw [actual_edge_reverse_zero (fullPrimes F) hd hp2 _ _ hs]
  exact theta_at_I_zero F i j

/-- The exact old/theta cross-row sums required to preserve the entire
small core follow from mutual PRODUCT squareness and the produced I bits. -/
theorem actual_full_cross_rows {d : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    {qB : BetaIndex d → ℕ} {qJ : J → ℕ} [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    {forbidden : Finset ℕ} {N : ℕ} (F : JointFamily d qB qJ forbidden N)
    (hB : Function.Injective qB) (hJ : Function.Injective qJ) (hdis : ∀ b j, qB b ≠ qJ j)
    (hcB : ∀ b, Nat.Coprime (qB b) 12) (hcJ : ∀ j, Nat.Coprime (qJ j) 12)
    (H : MutualSymbols qB qJ) :
    (∀ i : CoreIndex d, (∑ j : J, edges (fullPrimes F) (some (Sum.inl i)) (some (Sum.inr j)))=0) ∧
    (∀ j : J, (∑ b : BetaIndex d, edges (fullPrimes F) (some (Sum.inr j))
      (oldEmbedding (bIndex b)))=0) := by
  obtain ⟨hBJ,hJB⟩ := actual_mutual_rows qB qJ hdis H
  constructor
  · intro i
    cases i with
    | inl b =>
      simpa [edges,fullPrimes,adjoin,assembled,bIndex,betaRestriction] using hBJ b
    | inr i =>
      apply Finset.sum_eq_zero
      intro j _
      exact I_at_theta_zero F hB hJ hdis hcB hcJ i j
  · intro j
    simpa [edges,fullPrimes,adjoin,assembled,oldEmbedding,bIndex,betaRestriction] using hJB j

end ActualTwoDescentBetaThetaFamily318
